# BooleanGates.lean — Boolean Gates as ReLU Arithmetic

This file defines the seven Boolean gate types and implements each one
as a real-valued function using ReLU arithmetic. These are the atomic
computational units that the transformer's FFN layer computes.

## Why ReLU

Transformers use ReLU (or similar) nonlinearities in their FFN layers.
To prove that a transformer can compute Boolean circuits, we need to show
that each Boolean gate AND, OR, NOT, NAND, NOR, XOR, COPY can be expressed
exactly using the operations available in a two-layer ReLU network.

The key insight is that for inputs restricted to {0, 1}, ReLU arithmetic
is expressive enough to compute any Boolean function exactly, not just
approximately.

## The relu Function

relu x = max(0, x).

For Boolean inputs encoded as 0.0 and 1.0, a two-layer ReLU network with
appropriate weights can compute any of the standard gates. The proofs in
this file verify each gate formula by case-splitting on all input combinations.

## Gate Implementations

Each gate is implemented as a function from (ℝ, ℝ) to ℝ, designed to
return exactly 0.0 or 1.0 when inputs are in {0.0, 1.0}.

boolAnd a b = relu(a + b - 1.5) * 2.
When a=1, b=1: relu(0.5) * 2 = 1. All other cases: relu of negative = 0.
This is verified by the lemmas and_11, and_10, and_01, and_00.

boolOr a b = relu(a + b - 0.5) * 2, clamped to at most 1.
Equivalently implemented to return 1 when at least one input is 1.
Verified by or_11, or_10, or_01, or_00.

boolNot a = 1 - relu(a - 0.5) * 2, or equivalently relu(0.5 - a) * 2.
Returns 1 when a=0, returns 0 when a=1.
Verified by not_0, not_1.

boolNand a b = boolNot(boolAnd a b).
NAND is the complement of AND. Returns 0 only when both inputs are 1.

boolNor a b = boolNot(boolOr a b).
NOR is the complement of OR. Returns 1 only when both inputs are 0.

boolXor a b = relu(a + b - 0.5) * 2 - relu(a + b - 1.5) * 4, or similar.
Returns 1 when inputs differ, 0 when they agree.

boolCopy a _ = a.
Ignores the second input and returns the first. Used for COPY gates which
propagate a value unchanged.

## GateType

GateType is an inductive type with seven constructors:
AND, OR, NOT, NAND, NOR, XOR, COPY.

applyGate g a b — Dispatches on GateType g to apply the corresponding
Boolean function to Bool inputs a and b. Returns a Bool.

This is the specification: applyGate says what the gate should compute.
The real-valued implementations (boolAnd, boolOr, etc.) are shown to
match applyGate in FFNGateSelection.lean via realvalued_matches_bool.

## Correctness Lemmas

Each gate has a set of four lemmas (or two for NOT) verifying all input
combinations. For example for AND:

and_11: boolAnd 1 1 = 1. Proof: relu(1 + 1 - 1.5) * 2 = relu(0.5) * 2 = 1.
and_10: boolAnd 1 0 = 0. Proof: relu(1 + 0 - 1.5) * 2 = relu(-0.5) * 2 = 0.
and_01: boolAnd 0 1 = 0. Proof: relu(0 + 1 - 1.5) * 2 = relu(-0.5) * 2 = 0.
and_00: boolAnd 0 0 = 0. Proof: relu(0 + 0 - 1.5) * 2 = relu(-1.5) * 2 = 0.

All proofs go through by norm_num after unfolding relu as max and
substituting the concrete input values.

## Role in the Proof

BooleanGates.lean is the foundation of the FFN correctness argument.
FFNGateSelection.lean imports these definitions and uses the gate
implementations to build standardGates, the array of all seven gates
indexed by Fin 7. The realvalued_matches_bool theorem there combines
the individual gate lemmas with the one-hot selector argument to show
that the complete FFN computation matches applyGate.