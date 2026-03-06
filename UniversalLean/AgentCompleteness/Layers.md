# Layers.lean — The Four-Layer Transformer Construction

This file defines the concrete four-layer transformer that performs one
step of Boolean circuit simulation. It specifies exactly what each layer
does to the circuit state and assembles them into the forwardPass function.

## The Four Layers

The transformer is broken into four sequential operations on a CircuitState.

Layer 1 — gatherFirstInput:
Each token j reads the value from token wire1[j] and stores it in scratch1.
This implements the first attention head: query position j, key/value at wire1[j].
After this layer, scratch1[j] = state[wire1[j]].val for every token j.

Layer 2 — gatherSecondInput:
Each token j reads the value from token wire2[j] and stores it in scratch2.
This implements the second attention head: query position j, key/value at wire2[j].
After this layer, scratch2[j] = state[wire2[j]].val for every token j.

Layer 3 — computeGate:
Each token j applies its gate function to scratch1[j] and scratch2[j],
storing the result in val. This implements the FFN layer.
After this layer, val[j] = applyGate(gate[j], scratch1[j], scratch2[j]).

Layer 4 — updateWiring:
Each token j reads its program at its current iteration to get new wire1 and wire2.
This updates the wiring for the next forward pass, advancing the computation.
After this layer, wire1[j] and wire2[j] reflect the next phase's wiring.

## Key Definitions

GateWiring — A pair (wire1, wire2) of token indices. Specifies which two
tokens a given token should read from during the gather phases.

Program n depth — A function (Fin depth -> Fin n -> GateWiring n).
Maps each layer index and token index to a wiring specification.
The depth parameter bounds the number of distinct wiring configurations.

Token n depth — The full state of one token. Fields include: val (current
Boolean value), gate (GateType), wire1 and wire2 (wiring), scratch1 and
scratch2 (temporary registers), iteration (current program step),
and program (the fixed program for this token).

CircuitState n depth — A function Fin n -> Token n depth. The complete
state of the transformer: n tokens each with depth-many program steps.

gatherFirstInput state — Applies layer 1 to state. Returns a new CircuitState
where each token j has scratch1 set to state[state[j].wire1].val.
All other fields are copied unchanged.

gatherSecondInput state — Applies layer 2. Returns a new CircuitState
where each token j has scratch2 set to state[state[j].wire2].val.
All other fields are copied unchanged.

computeGate state — Applies layer 3. Returns a new CircuitState where
each token j has val set to applyGate(state[j].gate, state[j].scratch1,
state[j].scratch2). All other fields are copied unchanged.

updateWiring state — Applies layer 4. Returns a new CircuitState where
each token j has wire1 and wire2 updated from state[j].program at
state[j].iteration. All other fields are copied unchanged.

forwardPass state — Composes all four layers in sequence:
updateWiring(computeGate(gatherSecondInput(gatherFirstInput(state)))).
This is the single-step transformer operation.

## The Agent Loop

The agent loop is forwardPass iterated d times: forwardPass^[d].

Lean's Function.iterate provides this directly. The notation forwardPass^[d]
means apply forwardPass d times starting from the initial state.

Each application of forwardPass corresponds to one step of the TM being
simulated. After d applications starting from encode(cfg), the tape
region of the CircuitState reflects tmRun(delta, cfg, d).tape.

## Connection to Real Transformers

The four layers correspond to real transformer components as follows.

gatherFirstInput and gatherSecondInput correspond to two attention heads.
In a real transformer these would use softmax attention with positional
encoding keys and queries. AttentionLookup.lean proves that attention with
high enough temperature approximates the exact lookup implemented here.

computeGate corresponds to the FFN layer. In a real transformer this uses
ReLU nonlinearity with weight matrices. FFNGateSelection.lean proves that
the FFN with appropriate weights computes exactly applyGate.

updateWiring corresponds to a residual connection plus a learned projection
that reads the program stored in the token embedding and updates the
wire indices. This is the layer that makes the construction an agent
rather than a fixed-depth circuit: the program field encodes what to
do at each step of the agent loop.