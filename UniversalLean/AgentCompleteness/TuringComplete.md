# TuringComplete.lean — The Top-Level Turing Completeness Result

This file contains the two final theorems of the formalization:
agent_simulates_any_tm and transformer_is_turing_complete.

These are the formal versions of Corollary 5.3 in the paper.

## What Is Being Proved

We prove that a 4-layer transformer operating in an agent loop —
reading from an external tape, computing one forward pass, writing back —
can simulate any Turing machine for any number of steps.

This means transformers are universal computers, not merely function
approximators. The key point is that the agent loop provides the
unbounded iteration; each forward pass simulates one TM step.

## The Setup

A TM is given by its transition function delta : TMTransition k, where k
is the number of states. A configuration TMConfig k tapeLen holds the
current tape contents, head position, and machine state.

The transformer state is a CircuitState with fullTokenCount tapeLen k tokens.
This count covers: tapeLen tape tokens, bitWidth(tapeLen) head-position tokens,
bitWidth(k) state tokens, and a workspace region for the DNF circuit.

The encode function converts any TMConfig into an initial CircuitState.
The forwardPass function applies one transformer step.
The tmRun function applies the TM transition function d times.

## The Dependency Chain

TuringComplete.lean sits at the top of the following chain:

    BooleanGates: ReLU implements Boolean gates
        feeds into FFNGateSelection: FFN selects correct gate
        feeds into AttentionLookup: attention performs wire lookup
        feeds into Layers: 4-layer construction
        feeds into ProgramEncoding: program encodes TM transition via DNF
        feeds into TMCorrectness: forwardPass^d simulates tmRun d
        feeds into TuringComplete: exists initial state realizing any TM

## Main Theorems

agent_simulates_any_tm — For any TM (k states, tapeLen tape), transition
function delta, and initial config cfg, there exists a depth, an initial
CircuitState, such that (1) the initial state correctly decodes to cfg.tape,
and (2) for all d, after d forward passes the tape decodes to tmRun(delta, cfg, d).

The proof constructs depth = 3 (the minimum needed for the 3-phase program:
gather inputs, compute DNF, writeback). It takes state0 = encode(hk, hd, cfg),
verifies the tape decoding by unfolding encode, and applies
forwardPass_iter_simulates_tmRun with the wellformedness certificate
encode_wellformed.

transformer_is_turing_complete — A corollary with a slightly cleaner statement:
for any k, tapeLen, d, delta, cfg, there exists a CircuitState such that
forwardPass iterated d times decodes to tmRun(delta, cfg, d).

The proof is a one-liner: take state0 = encode(hk, hd, cfg) and apply
forwardPass_iter_simulates_tmRun with encode_wellformed.

## What Makes This Non-Trivial

The result is not immediate because transformers have fixed depth and width.
The key insight is that the agent loop provides iteration — the same 4-layer
network runs repeatedly, with the tape providing external memory. Each pass
executes one step of a DNF circuit that exactly computes the TM's transition
function, built via the minterm construction in FiniteCircuit.lean.

The number 4 in "4-layer" comes from the proof construction:
Layer 1 gathers wire1 into scratch1 (attention).
Layer 2 gathers wire2 into scratch2 (attention).
Layer 3 applies the gate function (FFN).
Layer 4 updates the wiring for the next step (copy with program lookup).