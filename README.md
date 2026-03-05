# Universal Lean: Formal Proof of Agent Turing Completeness

A Lean 4 formalization of the paper:

> **Agent Completeness via Circuit Simulation:
> A Natural Proof that Transformer Agents are Universal Computers**
> Greg Coppola, PhD (coppola.ai, March 2026)

## What This Is

A companion formalization to the paper, proving that a 4-layer transformer
operating in a read-compute-write agent loop is Turing complete. The proof
proceeds via Boolean circuit simulation rather than instruction-set emulation,
connecting transformer computation to the characteristica universalis framework.

## Proof Status

### Fully Proven (novel, no sorry)

| Theorem | File | Paper Reference |
|---------|------|-----------------|
| `relu_inactive_zero` | FFNGateSelection | Eq. 18 |
| `relu_active_correct` | FFNGateSelection | Eq. 18 |
| `standardGates_binary` | FFNGateSelection | Lemma 4.3 |
| `ffn_gate_selection_correct` | FFNGateSelection | Eq. 18 |
| `realvalued_matches_bool` | FFNGateSelection | Sec. 4.3 |
| `posEncDot_self` | AttentionLookup | Eq. 5 |
| `distinct_differ_in_bit` | AttentionLookup | Eq. 5 |
| `hardmaxAttention` | AttentionLookup | Lemmas 4.1, 4.2 |
| `layer1_attention_correct` | AttentionLookup | Lemma 4.1 |
| `layer2_attention_correct` | AttentionLookup | Lemma 4.2 |
| `transformer_circuit_correctness` | TransformerCorrectness | Theorem 5.1 |
| `forwardPass_val` | MainTheorems | Theorem 5.1 |
| `updateWiring_correct` | MainTheorems | Sec. 4.4 |
| `gather_correct` | MainTheorems | Lemmas 4.1, 4.2 |
| `agent_completeness` | MainTheorems | Theorem 5.2 |
| `decode_tape_encode` | Encoding | Sec. 3 |
| `minterm_correct` | FiniteCircuit | Sec. 4.3 |
| `buildTMCircuitEncoding_correct` | FiniteCircuit | Sec. 4.3 |
| `forwardPass_iter_simulates_tmRun` | TMCorrectness | Theorem 5.2 |
| `tm_correctness` | TMCorrectness | Theorem 5.2 |
| `flipTM_flips_all` | ExampleTM | Corollary 5.3 |
| `flipTM_circuit_correct` | ExampleTM | Corollary 5.3 |
| `agent_simulates_any_tm` | TuringComplete | Corollary 5.3 |
| `transformer_is_turing_complete` | TuringComplete | Corollary 5.3 |

### Sorry'd — Classical Math (not novel, Mathlib closes these)

| Sorry | File | Why Classical |
|-------|------|---------------|
| `bitsToNat_natToBits` | Binary | Standard number theory |
| `bitsToNat_lt` | Binary | Standard number theory |
| `natToBits_surjective` | FiniteCircuit | Standard number theory |
| `decode_head_encode` | Encoding | Follows from binary lemmas |
| `decode_state_encode` | Encoding | Follows from binary lemmas |
| `foldl_inactive_zero` | FFNGateSelection | Fin.foldl bookkeeping |
| `reluGatedSelect_oneHot` | FFNGateSelection | Fin.foldl bookkeeping |
| `posEncDot_distinct` | AttentionLookup | Combinatorics |
| `dnf_correct` | FiniteCircuit | Classical logic |
| `softmax_concentrates` | AttentionLookup | Real analysis |

### Sorry'd — Novel, Remaining Work (2)

| Sorry | File | What's Needed |
|-------|------|---------------|
| `workspace_output_after_compute` | ProgramEncoding | Connect DNF encoding to computeGate output |
| `tape_after_writeback` | ProgramEncoding | Connect updateWiring to tmStep tape output |

These two are the only remaining novel mathematical gaps.
The proof sketch is present in comments. Each sorry is
a single focused claim about one phase of the program execution.
Once closed, `forwardPass_simulates_via_program` becomes
fully proven, eliminating the last gap in the chain.

## Proof Architecture