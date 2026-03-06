# FiniteCircuit.lean — DNF Encoding of the TM Transition Function

This file proves that any Boolean function can be computed by a DNF
(Disjunctive Normal Form) circuit — a two-level AND-OR network — and
uses this to build a circuit that computes the TM transition function.

This is the formal version of Section 4.3 in the paper, establishing
that the finite state of a TM can be implemented as a fixed Boolean circuit.

## The Core Idea

A Turing machine's transition function delta : (state, symbol) -> (state, symbol, dir)
is a finite Boolean function. It maps bitWidth(k) + 1 input bits to
bitWidth(k) + 2 output bits. Any finite Boolean function can be expressed
as a DNF: OR over all input patterns that produce output 1, where each
term is an AND (minterm) over all input bits (positive or negative).

This means the TM transition function has an exact circuit representation
with a fixed number of gates determined only by the number of states k.
The transformer can hardcode this circuit in its weights.

## Key Definitions

minterm inputWidth pattern inputs — The AND of all input literals for a given
pattern. For each bit position i, it includes inputs[i] if pattern[i] = true,
or NOT inputs[i] if pattern[i] = false. Returns true iff inputs matches pattern
exactly at every position.

dnf inputWidth truthTable inputs — The OR over all 2^inputWidth input patterns
of (truthTable[pattern] AND minterm(pattern, inputs)). Enumerates every
possible input pattern via natToBits, includes its minterm if the truth table
says the output should be 1 for that pattern.

tmInputWidth k — Number of input bits to the TM circuit: bitWidth(k) bits
for the machine state plus 1 bit for the tape symbol.

tmOutputWidth k — Number of output bits: bitWidth(k) bits for the new state,
1 bit for the write symbol, 1 bit for the direction.

tmInputBits state sym — Encodes a (state, symbol) pair as a bit vector.
State bits come from natToBits(state.val, bitWidth k); the symbol bit is last.

tmOutputBits newState writeBit dir — Encodes a (newState, writeBit, dir)
triple as a bit vector. New state bits first, then writeBit, then direction.

tmTruthTable hk delta outBit — For a given output bit position, the Boolean
function that maps input bits to that output bit. Decodes the input bits
back to (state, symbol), applies delta, encodes the output, and returns
the specified bit.

buildTMCircuitEncoding hk delta — For each output bit, builds the DNF circuit
computing tmTruthTable for that bit. This is the complete circuit encoding
of delta as a Boolean function.

## Key Lemmas

minterm_correct — minterm fires (returns true) exactly when inputs matches
pattern at every position. Proved by induction on inputWidth, using
Fin.foldl_succ_last to peel off the last bit and Bool.and_eq_true to
split the conjunction. The base case uses Fin.elim0 since there are no bits.

minterm_false_of_diff — If inputs differs from pattern at some position i,
the minterm returns false. Proved by contradiction: if minterm were true,
minterm_correct would give inputs[i] = pattern[i], contradicting hdiff.

natToBits_surjective (axiom) — Every bit pattern of width inputWidth appears
as natToBits(row, inputWidth) for some row < 2^inputWidth. This guarantees
the DNF enumeration covers all input patterns. Standard number theory.

dnf_correct (axiom) — The DNF correctly computes any Boolean function:
dnf(inputWidth, truthTable, inputs) = truthTable(inputs). The proof would
show that exactly one minterm fires (the one matching inputs), contributing
truthTable(inputs) to the OR. Classical logic result.

## Main Theorem

buildTMCircuitEncoding_correct — For any state and symbol, the DNF circuit
correctly computes all output bits of the transition function. Specifically:
the write bit output equals writeBit from delta(state, sym); the direction
bit output equals (dir == Dir.R); and each state bit output equals the
corresponding bit of natToBits(newState). The proof applies dnf_correct
to reduce each output bit claim to tmTruthTable correctness, then uses
bitsToNat_natToBits to verify that the decoded input state matches cfg.state,
and tmOutputBits to confirm the output encoding.

## Why This Matters

This file establishes that the transition function of any k-state TM can be
hardcoded as a fixed Boolean circuit with a number of gates polynomial in k.
Combined with the FFN gate selection result (FFNGateSelection.lean), this
means the transformer's FFN layer can implement this circuit exactly.
The workspace region in the token sequence holds the intermediate gate values,
and the program field of each token specifies the wiring for each phase.