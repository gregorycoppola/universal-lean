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

**Complete. No sorries remain in novel claims.**

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
| `encode_wellformed` | ProgramEncoding | Sec. 3 |
| `copy_gate_preserves_val` | ProgramEncoding | Sec. 4.4 |
| `workspace_inputs_after_gather` | ProgramEncoding | Lemma 4.1 |
| `workspace_output_after_compute` | ProgramEncoding | Sec. 4.3 |
| `tape_after_writeback` | ProgramEncoding | Sec. 4.4 |
| `gate_preserved` | TMCorrectness | Sec. 4.4 |
| `wire1_after_forwardPass` | TMCorrectness | Sec. 4.4 |
| `wire2_after_forwardPass` | TMCorrectness | Sec. 4.4 |
| `state_bits_after_forwardPass` | TMCorrectness | Theorem 5.1 |
| `wellFormed_preserved` | TMCorrectness | Theorem 5.1 |
| `forwardPass_simulates_via_program` | ProgramEncoding | Theorem 5.1 |
| `forwardPass_simulates_tmStep` | TMCorrectness | Theorem 5.1 |
| `forwardPass_iter_simulates_tmRun` | TMCorrectness | Theorem 5.2 |
| `tm_correctness` | TMCorrectness | Theorem 5.2 |
| `flipTM_head_pos` | ExampleTM | Corollary 5.3 |
| `flipTM_state_after` | ExampleTM | Corollary 5.3 |
| `flipTM_tape_after_head` | ExampleTM | Corollary 5.3 |
| `flipTM_tape_before_head` | ExampleTM | Corollary 5.3 |
| `flipTM_flips_all` | ExampleTM | Corollary 5.3 |
| `flipTM_circuit_correct` | ExampleTM | Corollary 5.3 |
| `agent_simulates_any_tm` | TuringComplete | Corollary 5.3 |
| `transformer_is_turing_complete` | TuringComplete | Corollary 5.3 |

### Axiomatized (classical math, not novel)

These are well-known results assumed without proof.
Each corresponds to a standard textbook theorem.
A Mathlib import would close all of them automatically.

| Axiom | File | Why Classical |
|-------|------|---------------|
| `bitsToNat_natToBits` | Binary | Binary round trip. Standard number theory. |
| `bitsToNat_lt` | Binary | bitsToNat bounded by 2^width. Standard. |
| `bitsToNat_single` | Binary | Place value bound. Standard. |
| `natToBits_surjective` | FiniteCircuit | Every bit pattern enumerated. Standard. |
| `dnf_correct` | FiniteCircuit | DNF computes any Boolean function. Classical logic. |
| `distinct_differ_in_bit` | AttentionLookup | Distinct naturals differ in a bit. Number theory. |
| `posEncDot_distinct` | AttentionLookup | Distinct positions have dot product ≤ b-2. Combinatorics. |
| `softmax_concentrates` | AttentionLookup | Softmax approximates hardmax at high temperature. Real analysis. |
| `foldl_inactive_zero` | FFNGateSelection | Fold over inactive terms sums to zero. Lean bookkeeping. |

## Proof Architecture

    Boolean gates (BooleanGates.lean)
        ↓
    FFN gate selection (FFNGateSelection.lean)
        ↓
    Attention lookup (AttentionLookup.lean)
        ↓
    4-layer construction (Layers.lean)
        ↓
    Forward pass correctness (MainTheorems.lean)
        ↓
    TM encoding (Encoding.lean, Binary.lean)
        ↓
    DNF circuit encoding (FiniteCircuit.lean)
        ↓
    Program construction (ProgramEncoding.lean)
        ↓
    TM simulation (TMCorrectness.lean)
        ↓
    Turing completeness (TuringComplete.lean)

## File Structure

    UniversalLean/AgentCompleteness/
    ├── Preliminaries.lean          -- Token, CircuitState, GateType
    ├── Binary.lean                 -- natToBits, bitsToNat, axioms
    ├── BooleanGates.lean           -- ReLU gate implementations
    ├── FFNGateSelection.lean       -- Equation 18, gate selector
    ├── AttentionLookup.lean        -- Positional encoding, hardmax
    ├── Layers.lean                 -- 4 transformer layers
    ├── MainTheorems.lean           -- Theorems 5.1, 5.2
    ├── TuringMachine.lean          -- TM definition, tmStep, tmRun
    ├── Encoding.lean               -- encode, decode, round trips
    ├── FiniteCircuit.lean          -- minterm, DNF, TM circuit encoding
    ├── ProgramEncoding.lean        -- buildTransitionCircuit, phases
    ├── TMCorrectness.lean          -- forwardPass simulates tmRun
    ├── ExampleTM.lean              -- Concrete flipTM end-to-end
    ├── TransformerCorrectness.lean -- Unified correctness statement
    ├── TuringComplete.lean         -- agent_simulates_any_tm
    └── ProofSummary.lean           -- Proof index and status

## Setup

Install Lean 4 via elan:

    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

Then build (no Mathlib required):

    cd universal-lean
    lake build

## Relationship to the Paper Trilogy

This formalization is part of a three-paper series:

1. **Coppola (2024)** — The Quantified Boolean Bayesian Network
2. **Coppola (2026a)** — Statistical Parsing for Logical Information Retrieval
3. **Coppola (2026b)** — The Universal Language: A Characteristica Universalis for AI

The Turing completeness proof connects transformer computation
to the characteristica universalis framework via the correspondence:

| Circuit | Characteristica | Transformer |
|---------|----------------|-------------|
| Gate value | Proposition truth | Token embedding |
| Wiring | Role binding | Attention pattern |
| Gate type | Inference rule | FFN computation |
| Circuit layer | Inference step | Forward pass |
| Agent loop | Iterated inference | Read-compute-write |

## Citation

    @misc{coppola2026agent,
      title={Agent Completeness via Circuit Simulation:
             A Natural Proof that Transformer Agents are
             Universal Computers},
      author={Coppola, Greg},
      year={2026},
      url={https://coppola.ai}
    }