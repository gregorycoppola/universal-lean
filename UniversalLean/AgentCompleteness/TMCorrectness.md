# TMCorrectness.lean — Iterated Forward Passes Simulate tmRun

This file proves by induction that running forwardPass d times starting
from a WellFormed initial state produces a tape matching tmRun(delta, cfg, d).
It also proves that WellFormed is preserved at each step, making the
induction go through.

## The Central Challenge

A single step result (forwardPass_simulates_via_program) is not enough.
We need to show that after d steps the tape still correctly reflects the
TM state. This requires two things:

First, that WellFormed is an invariant — if we start in a WellFormed state
for cfg, then after one forwardPass we are in a WellFormed state for
tmStep(delta, cfg). This is wellFormed_preserved.

Second, that iterated application of WellFormed-preserving steps simulates
iterated TM steps. This is forwardPass_iter_simulates_tmRun, proved by
induction on d.

## Structural Lemmas

gate_preserved — The gate field of every token is unchanged by forwardPass.
Proved by unfolding forwardPass, updateWiring, computeGate, and observing
that none of these functions modify the gate field.

wire1_after_forwardPass — After forwardPass, wire1 of token j equals
program[iteration[j]][j].wire1. This is exactly what updateWiring does:
it reads the program at the current iteration to set wire1 and wire2.

wire2_after_forwardPass — Same as wire1_after_forwardPass for wire2.

state_bits_after_forwardPass — After forwardPass, the state region tokens
hold natToBits(newState) where newState comes from delta(cfg.state, cfg.tape[cfg.head]).
The proof traces through phase3Wiring (state tokens wire to workspace output),
computeGate (workspace output holds DNF result), and workspace_output_after_compute
(DNF result matches transition function output).

## The Invariant Preservation Proof

wellFormed_preserved — If state is WellFormed for cfg, then forwardPass(state)
is WellFormed for tmStep(delta, cfg). The proof checks each field of WellFormed:

tape_gate: gate fields are unchanged (gate_preserved).
tape_wire1: tape tokens get identity wiring from phase3Wiring (not in state region),
so wire1 = j after forwardPass. Proved using wire1_after_forwardPass and
the phase3Wiring definition.
tape_wire2: same argument for wire2.
tape_val: follows from tape_after_writeback, which connects the COPY gate
preservation and head writeback to tmStep.tape.
state_val: follows from state_bits_after_forwardPass.

## The Induction

forwardPass_iter_simulates_tmRun — For any d, if state0 is WellFormed for cfg,
then decodeTape(forwardPass^d(state0)) = tmRun(delta, cfg, d).tape.

Base case (d=0): forwardPass^0 = identity. decodeTape(state0) = cfg.tape
by hwf.tape_val. tmRun(delta, cfg, 0) = cfg by definition.

Inductive step (d = succ d'): We need decodeTape(forwardPass^(d'+1)(state0))
= tmRun(delta, cfg, d'+1).tape. Rewrite iterate succ as forwardPass composed
with forwardPass^d'. Apply the inductive hypothesis to forwardPass(state0)
with the new config tmStep(delta, cfg) and the new wellformedness certificate
wellFormed_preserved. This matches tmRun(delta, tmStep(delta,cfg), d').tape
= tmRun(delta, cfg, d'+1).tape by the definition of tmRun.

## Top-Level Correctness

tm_correctness — Wraps forwardPass_iter_simulates_tmRun with d = depth.
For any WellFormed initial state, running depth forward passes produces
the tape after depth TM steps. This is the theorem that TuringComplete.lean
calls to establish the final result.