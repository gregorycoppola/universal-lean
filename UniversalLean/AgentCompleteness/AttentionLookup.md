# AttentionLookup.lean — How Attention Performs Wire Lookup

This file proves that transformer attention can retrieve the value stored
at any specified position — implementing the "wire lookup" that a Boolean
circuit needs to connect gate outputs to gate inputs.

This is the formal version of Lemmas 4.1 and 4.2 in the paper.

## The Core Idea

A Boolean circuit has gates connected by wires. When gate j computes its
output, it needs to read the current values at wire1[j] and wire2[j].
Attention performs this lookup using positional encodings as keys and queries.

Each token at position i has a positional encoding posEnc(b, i): a vector
in {-1, +1}^b where bit k is +1 if bit k of i is 1, else -1.

The dot product posEncDot(b, i, j) = sum_k posEnc(b,i,k) * posEnc(b,j,k).

When i = j: every term is (+1)*(+1) or (-1)*(-1) = +1, so the sum = b.
When i ≠ j: at least one bit differs, contributing -1, so the sum ≤ b-2.

This gap of at least 2 means softmax at high enough temperature concentrates
all weight on the matching position — implementing exact lookup.

## Key Definitions

posEnc — Positional encoding for position i as a {-1,+1}^b vector.
Uses bit k of i: +1 if the k-th bit is 1, -1 if it is 0.

posEncDot — Inner product of two positional encodings. This is the attention
score between a query at position i and a key at position j.

hardmaxAttention — The idealized (temperature → infinity) attention that
returns the exact position with the highest dot product score.

## Key Lemmas

posEncDot_self — Self dot product equals b. Proved by induction: each of
the b terms is posEnc(i,k)^2 = 1, so the fold accumulates to b.

posEnc_sq — Each term posEnc(i,k) * posEnc(i,k) = 1. Proved by case split
on whether bit k of i is 0 or 1.

posEnc_term_pm1 — Each cross term posEnc(i,k) * posEnc(j,k) is either +1
or -1. Proved by case split using posEnc_same_term and posEnc_diff_term.

posEncDot_le_b — The dot product of any two encodings is at most b. Proved
by induction on b: each term contributes at most +1, so the fold is bounded
by the number of terms.

posEncDot_with_diff_term — If a specific term k contributes -1, the total
dot product is at most b-2. Proved by induction on b, case splitting on
whether k is the last term or lies in the first b terms.

distinct_differ_in_bit (proven) — If i ≠ j and both are less than 2^b,
they differ in at least one bit position. Proved by contradiction: if all
bits agree then natToBits i b = natToBits j b, which by natToBits_inj
implies i = j, contradicting the hypothesis.

posEncDot_distinct (proven) — If i ≠ j, their dot product is at most b-2.
Proved by combining distinct_differ_in_bit (which gives a differing bit k),
posEnc_diff_term (the term at k equals -1), and posEncDot_with_diff_term
(one -1 term forces the total to be at most b-2).

posEncDot_self_max — The self dot product b strictly exceeds any cross dot
product (at most b-2). Direct consequence of posEncDot_distinct.

softmax_concentrates (axiom) — With temperature lambda = O(log(n/eps)/2),
the softmax weight on the maximum-score position is at least 1-eps.
Standard real analysis result from ML theory.

## Main Theorems

hardmaxAttention — Given injective keys and a query present among them,
there exists a unique position i* with keys[i*] = query, and all other
positions have strictly lower dot product with the query. The proof finds
i* from hPresent, then applies posEncDot_self_max to show all others are lower.

layer1_attention_correct — After gatherFirstInput, scratch1 of token j holds
the value of the token at wire1[j]. Proved by unfolding gatherFirstInput,
which directly reads state[state[j].wire1].val into scratch1.

layer2_attention_correct — After gatherSecondInput, scratch2 of token j holds
the value of the token at wire2[j]. Proved similarly.

attention_approximates_lookup — There exists a temperature lambda such that
softmax attention places weight >= 1-eps on the correct lookup position.
The proof constructs lambda = log(n/eps)/2 and invokes hardmaxAttention.

## Connection to the Circuit

In our 4-layer construction, Layer 1 implements gatherFirstInput and Layer 2
implements gatherSecondInput. Together they load both wire values into the
scratch registers of each token, ready for the FFN (Layer 3) to apply the gate.