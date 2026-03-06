# Preliminaries.lean — Core Data Structures

This file defines the fundamental types used throughout the formalization:
Token, CircuitState, GateType, and the associated operations. Everything
else in the proof is built on top of these definitions.

## Design Philosophy

The formalization models a transformer as operating on a sequence of tokens,
each carrying enough state to participate in Boolean circuit simulation.
Rather than modeling weight matrices and matrix multiplication directly,
we work at the level of what each token computes — which is the right level
for a correctness proof about the agent loop.

## GateType

An inductive enumeration of the seven supported Boolean gate types:
AND, OR, NOT, NAND, NOR, XOR, COPY.

applyGate : GateType -> Bool -> Bool -> Bool dispatches to the correct
Boolean function for each gate type. This is the ground truth specification
that the real-valued transformer computation is proved to match.

## GateWiring

A structure with two fields: wire1 and wire2, both of type Fin n.
Specifies which two token positions a given token should read from
during the gather phases. This is the discrete analogue of the attention
pattern in a real transformer.

## Program

Program n depth = Fin depth -> Fin n -> GateWiring n.

A program specifies the wiring for each token at each step of the agent loop.
The depth parameter bounds how many distinct wiring configurations are needed.
In the TM simulation, depth = 3 suffices: one configuration per phase
(input loading, computation, writeback).

The program field is stored inside each token, meaning every token carries
a copy of the full program. This is a modelling choice that simplifies
the formalization — in a real transformer the program would be encoded
in shared weight matrices.

## Token

Token n depth is a structure with the following fields:

val : Bool — the current Boolean value computed at this token position.
This is the primary output: after computeGate, val holds the gate result.

gate : GateType — which Boolean gate this token computes.
Fixed throughout the simulation for circuit tokens; COPY for tape tokens.

wire1 : Fin n — index of the first input token.
wire2 : Fin n — index of the second input token.
Updated each step by updateWiring according to the program.

scratch1 : Bool — temporary register loaded by gatherFirstInput.
Holds state[wire1].val after the first attention layer.

scratch2 : Bool — temporary register loaded by gatherSecondInput.
Holds state[wire2].val after the second attention layer.

iteration : Fin depth — current program step index.
Determines which wiring configuration is active. Incremented each pass.

program : Program n depth — the fixed wiring schedule for this token.
Consulted by updateWiring to determine the next wire1 and wire2.

## CircuitState

CircuitState n depth = Fin n -> Token n depth.

The complete transformer state: a function from token index to token.
Using a function rather than a vector simplifies the Lean proofs since
function extensionality (funext) can be used to prove state equality.

n is the number of tokens (circuit width).
depth is the program depth (number of agent loop phases).

## The Computation Model

The transformer operates on CircuitState by applying four operations in
sequence (defined in Layers.lean): gatherFirstInput, gatherSecondInput,
computeGate, updateWiring. The result of composing these is forwardPass.

The agent loop is forwardPass iterated d times. Each iteration corresponds
to one step of the Turing machine being simulated. The tape region of the
CircuitState (the first tapeLen tokens) always holds the current tape contents,
readable by decodeTape at any point in the computation.

## Why This Model Is Faithful

The Token structure captures exactly the information flow in a transformer:
attention reads from other positions (wire1, wire2) into local registers
(scratch1, scratch2), the FFN applies a nonlinear function (gate) to produce
a new value (val), and a residual/projection updates the routing (wire1, wire2)
for the next step (program, iteration). The formalization makes this
information flow explicit and verifiable.