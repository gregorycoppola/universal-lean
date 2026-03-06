# Binary.lean — Bit Representation of Natural Numbers

This file defines the binary encoding of natural numbers as Boolean vectors
and establishes the basic lemmas needed to work with these representations
throughout the formalization.

## Why Binary Encoding

The transformer works with Boolean-valued tokens. Natural numbers that appear
in the TM — machine state index, head position — must be stored as sequences
of Boolean token values. Binary encoding is the standard choice: a natural
number n is stored as bitWidth(n) tokens, where token i holds bit i of n.

## Key Definitions

natToBits n width — Converts natural number n to a Boolean vector of length
width. The bit at position i is (n >>> i) % 2 == 1, i.e. the i-th bit of n
in binary. This is a function Fin width -> Bool.

bitsToNat width bits — Converts a Boolean vector back to a natural number.
Computes the sum over all positions i of (if bits[i] then 2^i else 0).
Uses Fin.foldl to accumulate the sum.

bitWidth n — The number of bits needed to represent n: Nat.log2(n) + 1.
This is the minimum width such that n < 2^bitWidth(n).

## Axioms

These are classical number theory facts stated as axioms. Each is a standard
result that any algorithms or discrete mathematics textbook would cover.
A Mathlib import would provide formal proofs.

bitsToNat_natToBits width n h — The round-trip: if n < 2^width, then
bitsToNat(width, natToBits(n, width)) = n. This is the fundamental
correctness property of binary representation.

bitsToNat_lt width bits — The bound: bitsToNat(width, bits) < 2^width.
A width-bit number always represents a value less than 2^width.

bitsToNat_single width bits i — Place value lower bound: the contribution
of bit i is at most bitsToNat. Each bit contributes a nonnegative amount.

## Derived Lemmas

natToBits_spec — The bit at position i of natToBits(n, 32) is true iff
(n >>> i) % 2 = 1. Direct unfolding of the definition.

natToBits_inj — natToBits is injective on [0, 2^width). If two numbers
have the same bit representation, they are equal. Proved using the round-trip
axiom: m = bitsToNat(natToBits(m)) = bitsToNat(natToBits(n)) = n.

natToBits_zero — natToBits(0, width) is all false. Proved by simp since
(0 >>> i) % 2 = 0 for all i.

bitWidth_sufficient — n < 2^(Nat.log2(n) + 1). Uses Nat.lt_pow_succ_log_self
from Lean's standard library.

bitWidth_spec — n < 2^bitWidth(n). Direct consequence of bitWidth_sufficient.
Used throughout to discharge the bound hypothesis in bitsToNat_natToBits calls.

## Role in the Proof

Binary.lean is imported by almost every other file in the formalization.
The encode/decode functions in Encoding.lean use natToBits and bitsToNat
to store and retrieve head position and machine state. The circuit encoding
in FiniteCircuit.lean uses natToBits to enumerate all input patterns for
the DNF construction. The attention mechanism in AttentionLookup.lean uses
the bit structure of positions for the positional encoding dot product.
The axioms here — particularly bitsToNat_natToBits — are the deepest
mathematical facts assumed in the entire proof.