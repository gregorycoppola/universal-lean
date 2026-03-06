# ProgramEncoding.lean — Encoding the TM Transition as a Transformer Program

This file is the bridge between the abstract TM and the concrete transformer.
It builds a three-phase program that instructs the transformer how to simulate
one step of any Turing machine, and proves that following this program
correctly executes the TM transition function.

## The Three-Phase Structure

Each forward pass simulates one TM step in three phases, controlled by
the program field of each token (which maps layer index to wiring instructions).

Phase 1 (layer 1, phase1Wiring): Load inputs into workspace.
The workspace input tokens wire themselves to the state region and tape head,
copying the current machine state bits and the symbol under the head into
the workspace input area. After this gather phase, the workspace holds
tmInputBits(cfg.state, cfg.tape[cfg.head]).

Phase 2 (layer 2, compute): Apply the DNF circuit.
The workspace output tokens have gates set up by buildTMCircuitEncoding.
The FFN applies these gates to compute the transition function output:
new state bits, write bit, and direction bit.

Phase 3 (layer 3, phase3Wiring): Write back results.
The state region tokens wire themselves to the workspace output area,
copying new state bits back. Tape tokens at the head position copy
the write bit. All other tape tokens have identity wiring and COPY gates,
preserving their values.

## Key Definitions

fullTokenCount tapeLen k — Total token count: tmTokenCount (tape + head + state)
plus tmCircuitSize (workspace input + output tokens for the DNF circuit).

phase1Wiring — Wiring instructions for the input-loading phase. Workspace
input tokens at offset i wire to the state region (for i < bitWidth k)
or to position 0 (as a proxy for the tape head symbol, refined in the proof).

phase3Wiring — Wiring instructions for the writeback phase. State region
tokens (indices tapeLen + bitWidth(tapeLen) .. + bitWidth(k)) wire to the
corresponding workspace output tokens. All other tokens get identity wiring.

buildProgram / buildTransitionCircuit — Assembles the full Program by
dispatching on layer index: layer 0 gets identity wiring, layer 1 gets
phase1Wiring, layer 2+ gets phase3Wiring.

WellFormed — A predicate on CircuitState capturing the invariant maintained
across steps. It asserts: tape tokens have COPY gate and self-wiring; tape
token values match cfg.tape; state region bits match natToBits(cfg.state).

## Key Lemmas

encode_wellformed — The initial state produced by encode satisfies WellFormed.
Proved by unfolding encode and defaultToken and checking each field directly.

copy_gate_preserves_val — A token with COPY gate and self-wiring has its
val field preserved through computeGate. Proved by unfolding computeGate,
gatherFirstInput, gatherSecondInput and simplifying with the gate and wire
hypotheses.

workspace_inputs_after_gather — After gatherFirstInput, workspace input tokens
hold exactly tmInputBits(cfg.state, cfg.tape[cfg.head]). The proof splits on
whether the input index is a state bit (i < bitWidth k) or the symbol bit,
then uses hwf.state_val and hwf.tape_val to match the expected bit values.

workspace_output_after_compute — After computeGate, workspace output tokens
hold tmOutputBits(newState, writeBit, dir). The proof uses
buildTMCircuitEncoding_correct and dnf_correct to connect the DNF circuit
gates to the transition function output, case-splitting on whether the output
index is a state bit, the write bit, or the direction bit.

tape_after_writeback — After updateWiring, tape token values match
tmStep(delta, cfg).tape. For tokens not at the head, COPY gate preserves
the original value (from hwf.tape_val). For the token at the head, the
write bit is read from the workspace output via hOutputs.

## Main Theorem

forwardPass_simulates_via_program — One forwardPass on a WellFormed state
produces a tape that matches tmStep(delta, cfg).tape. The proof chains the
three phase lemmas: workspace_inputs_after_gather gives hInputs,
workspace_output_after_compute uses hInputs to give hOutputs, and
tape_after_writeback uses hOutputs to conclude.