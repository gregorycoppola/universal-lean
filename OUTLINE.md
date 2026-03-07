# Proof Outline: Transformer Agents are Turing Complete

This is the entry point for understanding the formalization.
The main result is that a 4-layer transformer operating in an agent loop
can simulate any Turing machine for any number of steps.

The paper is here:
[paper-drafts/attention-agent-turing-complete.pdf](paper-drafts/attention-agent-turing-complete.pdf)

The full theorem list is in [README.md](README.md).

---

## The Main Result

[TuringComplete.lean](UniversalLean/AgentCompleteness/TuringComplete.lean)
/
[guide](UniversalLean/AgentCompleteness/TuringComplete.md)

For any Turing machine (transition function delta, k states, tape length L),
there exists an initial CircuitState such that running forwardPass d times
produces a tape matching d steps of the TM. The transformer has exactly
4 layers and a fixed width determined by k and L.

---

## The Proof in Three Steps

### Step 1: The Transformer Can Compute Any Boolean Gate

A Boolean circuit is built from AND, OR, NOT and related gates.
The transformer's two components — attention and FFN — each handle one part.

Attention performs wire lookup: given a query position j, it retrieves
the value stored at positions wire1[j] and wire2[j]. This is proved using
positional encodings whose dot products are maximized at the matching position.

[AttentionLookup.lean](UniversalLean/AgentCompleteness/AttentionLookup.lean)
/
[guide](UniversalLean/AgentCompleteness/AttentionLookup.md)

The FFN applies the gate: given a one-hot selector identifying the gate type,
a two-layer ReLU network computes the correct Boolean output exactly.

[FFNGateSelection.lean](UniversalLean/AgentCompleteness/FFNGateSelection.lean)
/
[guide](UniversalLean/AgentCompleteness/FFNGateSelection.md)

[BooleanGates.lean](UniversalLean/AgentCompleteness/BooleanGates.lean)
/
[guide](UniversalLean/AgentCompleteness/BooleanGates.md)

Together these give: one forward pass correctly simulates one layer of a
Boolean circuit.

[Layers.lean](UniversalLean/AgentCompleteness/Layers.lean)
/
[guide](UniversalLean/AgentCompleteness/Layers.md)

[MainTheorems.lean](UniversalLean/AgentCompleteness/MainTheorems.lean)

### Step 2: Any TM Transition Function Is a Boolean Circuit

A Turing machine with k states has a transition function that maps
(state, symbol) to (new state, write bit, direction). This is a finite
Boolean function and can be expressed exactly as a DNF circuit — a
two-level AND-OR network whose size depends only on k.

The DNF is built by enumerating all input patterns (minterms) and OR-ing
together those that produce a 1 output. This is classical logic.

[FiniteCircuit.lean](UniversalLean/AgentCompleteness/FiniteCircuit.lean)
/
[guide](UniversalLean/AgentCompleteness/FiniteCircuit.md)

The TM configuration (tape, head, state) is encoded as a CircuitState
with tape tokens, binary-encoded head position tokens, and binary-encoded
state tokens. The encoding and decoding are proved to be inverses.

[Encoding.lean](UniversalLean/AgentCompleteness/Encoding.lean)
/
[guide](UniversalLean/AgentCompleteness/Encoding.md)

[Binary.lean](UniversalLean/AgentCompleteness/Binary.lean)
/
[guide](UniversalLean/AgentCompleteness/Binary.md)

[TuringMachine.lean](UniversalLean/AgentCompleteness/TuringMachine.lean)
/
[guide](UniversalLean/AgentCompleteness/TuringMachine.md)

### Step 3: The Agent Loop Provides Unbounded Iteration

A single forward pass simulates one TM step. The agent loop — forwardPass
iterated d times — therefore simulates d TM steps. The proof proceeds by
induction on d, using a WellFormed invariant that tracks the correspondence
between the CircuitState and the current TMConfig at each step.

[ProgramEncoding.lean](UniversalLean/AgentCompleteness/ProgramEncoding.lean)
/
[guide](UniversalLean/AgentCompleteness/ProgramEncoding.md)

[TMCorrectness.lean](UniversalLean/AgentCompleteness/TMCorrectness.lean)
/
[guide](UniversalLean/AgentCompleteness/TMCorrectness.md)

---

## Data Structures

The proof is built on a small set of core types defined in:

[Preliminaries.lean](UniversalLean/AgentCompleteness/Preliminaries.lean)
/
[guide](UniversalLean/AgentCompleteness/Preliminaries.md)

The key types are Token (one position in the transformer), CircuitState
(the full transformer state), and Program (the wiring schedule that the
agent follows across steps).

---

## Axioms

Seven classical mathematical facts are stated as axioms rather than proved.
These are all standard results — binary representation round-trips, DNF
completeness, softmax concentration — that Mathlib would close automatically.
No novel claim is axiomatized.

The full list is in [README.md](README.md) under the Axiomatized section.

---

## Concrete Example

A concrete end-to-end example — a TM that flips all bits on the tape —
is fully proved in:

[ExampleTM.lean](UniversalLean/AgentCompleteness/ExampleTM.lean)

This verifies that the transformer correctly simulates flipTM for any
tape length, giving a ground-level sanity check on the whole construction.

---

## Proof Status Summary

[ProofSummary.lean](UniversalLean/AgentCompleteness/ProofSummary.lean)

Contains a machine-checked index of all theorems via hash-check statements,
confirming the full chain compiles without novel sorries.