# FFNGateSelection.lean — How the FFN Computes Boolean Gates

This file proves that a two-layer ReLU feedforward network (FFN) can compute
any Boolean gate — AND, OR, NOT, NAND, NOR, XOR, COPY — when given a one-hot
selector vector identifying which gate to apply.

This is the formal version of Equation 18 in the paper.

## The Core Idea

A transformer FFN has the form: output = W2 * ReLU(W1 * x + b1) + b2.

We model this as a sum over G=7 gate types. For each gate t, the FFN computes:

    relu(selector[t] + gate_t(a, b) - 1.5) * 2

When selector[t] = 1 (active): relu(1 + f - 1.5) * 2 = f, for f in {0,1}.
When selector[t] = 0 (inactive): relu(0 + f - 1.5) * 2 = 0, for f in {0,1}.

So only the active gate contributes to the sum.

## Key Definitions

reluGatedSelect — The real-valued FFN computation. Takes G, a selector vector,
a family of gate functions, and inputs a, b. Returns the sum of relu-gated
contributions from each gate.

standardGates — The seven Boolean gates implemented as real-valued functions
using ReLU arithmetic: AND, OR, NOT, NAND, NOR, XOR, COPY.

gateSelector — Builds the one-hot selector vector for a given GateType.
Returns 1.0 at the index for that gate, 0.0 everywhere else.

gateTypeToFin — Maps GateType to its index in Fin 7.

## Key Lemmas

relu_inactive_zero — When selector = 0, the relu term is 0 regardless of
the gate output. Proof: direct arithmetic on cases f=0, f=1.

relu_active_correct — When selector = 1, the relu term equals the gate output.
Proof: direct arithmetic on cases f=0, f=1.

standardGates_binary — The output of standardGates is always in {0,1} when
inputs are in {0,1}. Proved by case-splitting on all 7 gates and both inputs.

foldl_inactive_zero (axiom) — The fold over all inactive positions sums to
zero. This is a Lean bookkeeping fact about Fin.foldl; it requires induction
over the fold but contains no mathematical content.

## Main Theorems

reluGatedSelect_oneHot — With a one-hot selector identifying gate t*, the
reluGatedSelect sum equals exactly standardGates[t*](a, b). The proof splits
the fold into the one active term and all inactive terms, applies
relu_active_correct and foldl_inactive_zero respectively.

ffn_gate_selection_correct — The FFN with gateSelector(g) computes
standardGates[gateTypeToFin(g)](a, b). Direct application of
reluGatedSelect_oneHot using gateSelector_active and gateSelector_inactive.

realvalued_matches_bool — The real-valued FFN output on inputs in {0.0, 1.0}
matches the Boolean applyGate output converted to {0.0, 1.0}. Proved by
exhaustive case-split over all 7 gates and all 4 input combinations (28 cases).
This is the bridge between the real-valued transformer and the Boolean circuit.