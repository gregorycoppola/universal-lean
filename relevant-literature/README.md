# Relevant Literature — Index and Meta-Review

## Papers in This Directory

| File | Paper | Venue |
|---|---|---|
| perez-barcelo-marinkovic-review.md | Pérez, Barceló & Marinkovic — "Attention is Turing Complete" | JMLR 2021 |
| giannou-et-al-looped-transformers-review.md | Giannou et al. — "Looped Transformers as Programmable Computers" | ICML 2023 |
| wei-chen-ma-review.md | Wei, Chen & Ma — "Statistically Meaningful Approximation" | NeurIPS 2023 |

The primary paper under formalization is:

    Coppola, G. (2026). Agent Completeness via Circuit Simulation:
    A Natural Proof that Transformer Agents are Universal Computers.

---

## The Progression of the Field

These four papers form a natural research arc. Each addresses a limitation of
the previous work.

**Pérez et al. (2021)** established the foundational result: transformers are
Turing complete based on their intrinsic mechanism, not by architectural
extension. The construction uses a 3-layer decoder that autoregressively builds
the TM computation history. The critical limitation: it requires arbitrary
precision in the positional encodings (values 1/i and 1/i^2), and the authors
prove explicitly that fixed-precision transformers are NOT Turing complete under
their framework.

**Giannou et al. (2023)** made the construction explicit and programmable. By
using a looped transformer — the same network applied repeatedly — they showed
you could run arbitrary programs (sorting, linear algebra, in-context learning)
on a 9-13 layer transformer. This introduced the loop as an architectural
primitive, which is the key structural move that Coppola (2026) inherits and
clarifies. The limitation: 9-13 layers, and the attention mechanism is
reverse-engineered to perform CPU-style memory operations rather than
content-addressable lookup.

**Wei et al. (2023)** addressed the statistical side: prior constructions used
hardcoded weights and said nothing about learnability. Wei et al. proved that
transformers can approximate Turing machines with sample complexity polynomial
in log T — essentially showing the construction is not just expressively
sufficient but learnable in principle. They also used binary positional encodings
(log T bits) rather than arbitrary precision, an important step toward
realizability. The limitation: the decoder sequence still grows with T, depth
is O(log T), and there is no explicit agent loop.

**Coppola (2026)** synthesizes and sharpens all three lines:

- From Giannou: the loop as the source of unbounded computation
- From Wei: binary (bounded precision) positional encodings
- New: constant depth (4 layers), natural use of attention, typed proposition
  encoding, and the explicit agent loop as the formal model

---

## The Central Claim of Coppola (2026)

The prior three papers all prove Turing completeness by encoding unbounded
computation *inside* the transformer — either in a growing decoder sequence
(Pérez, Wei) or in a looped network that simulates a CPU (Giannou). In all
cases, the transformer itself is doing the bookkeeping of the computation.

Coppola (2026) makes a different architectural claim: **the transformer should
do bounded computation, and the agent loop should provide unbounded iteration.**
This is not just a cleaner proof strategy — it is the architecturally correct
model of how transformers are actually deployed as agents.

The result is:

- A **4-layer** transformer (vs. 9-13 for Giannou, O(log T) for Wei, 4 for
  Pérez but with arbitrary precision)
- **Bounded precision**: O(log n) bits for binary positional encodings of gate
  indices, independent of computation time
- **Natural attention**: each attention head performs content-addressable lookup
  (query a position, retrieve a value) — the same operation trained transformers
  perform over token sequences
- **The agent loop as a formal primitive**: Turing completeness is proved for
  the agent, not for a transformer with a long sequence

---

## Comparison Table

| Property | Pérez (2021) | Giannou (2023) | Wei (2023) | Coppola (2026) |
|---|---|---|---|---|
| Depth | 1+3 layers | 9-13 layers | O(log T) layers | 4 layers |
| Precision | Arbitrary | Not analyzed | O(log log T) | O(log n) — bounded |
| Iteration mechanism | Autoregressive decoder | Looped transformer | Autoregressive decoder | Explicit agent loop |
| Sequence grows with T? | Yes | No | Yes | No |
| Attention role | Position lookup via 1/i | CPU memory transfer | Binary search | Content-addressable lookup |
| FFN role | Transition function | Binary subtraction | Transition function | Gate computation |
| Proof strategy | Direct TM simulation | OISC/SUBLEQ | Circuit + SM approx | Boolean circuit simulation |
| Fixed precision TC? | No (proven negative) | Yes | Yes | Yes |
| Statistical learnability? | No | No | Yes | Open |
| Typed proposition framing? | No | No | No | Yes |
| Agent loop explicit? | No | Partial | No | Yes |

---

## What Makes Coppola (2026) Different

### 1. The Agent Loop is the Right Model

Real AI systems — tool-calling LLMs, autonomous agents, agentic pipelines —
operate in a read-compute-write loop. The transformer runs, produces output,
that output modifies state, the transformer runs again. This is the model
Coppola (2026) formalizes. Prior work proved Turing completeness of a
transformer-as-a-sequence-processor, which is not how agents work.

The formal statement of Theorem 5.2 is about an agent:

    St+1 = T(St),  S0 = E(x, Cf)

The transformer T is always the same 4-layer network. The agent loop provides
all scaling. This matches deployment reality.

### 2. Bounded Precision is Physically Realizable

Pérez et al. explicitly prove that fixed-precision transformers are not Turing
complete under their construction. Coppola (2026) requires only O(log n) bits —
the binary encoding of gate indices up to circuit size n. This is a small finite
number, implementable in standard floating-point arithmetic for any realistic
circuit. The construction is not just theoretically valid but physically
realizable.

### 3. Attention Does What Attention Does

In every prior construction, attention is reverse-engineered to perform some
operation it was not designed for: position lookup via arithmetic on 1/i
encodings (Pérez), CPU memory transfer indexed by program counter (Giannou),
binary search over past decoder states (Wei).

In Coppola (2026), attention performs **content-addressable lookup**: Layer 1
queries wire1_j against pos_l to retrieve v_{i1(j)}, the value at the first
input gate. Layer 2 queries wire2_j against pos_l to retrieve v_{i2(j)}, the
second input. This is exactly the operation trained transformers perform when
they retrieve relevant tokens from context. The proof mechanism and the
deployment mechanism are the same thing.

### 4. The Typed Proposition Connection

The circuit state representation:

    gate(pos: j, val: vj, type: gj, in1: i1(j), in2: i2(j))

is a knowledge base of typed propositions in the sense of the characteristica
universalis framework (Coppola 2024, 2026a, 2026b). One forward pass implements
one step of forward-chaining inference: attention performs universal
instantiation (binding role variables to specific proposition identifiers),
the FFN performs modus ponens (applying the gate rule to derive the output bit).

This connection is not present in any prior work. It provides a principled
account of *why* transformers compute naturally over structured knowledge — not
just that they can, but that the architecture corresponds to the natural
operations of logical inference over typed predicates.

### 5. Fewer Layers with Cleaner Separation

The 4 layers of Coppola (2026) each have a single, transparent purpose:

- Layer 1: Gather first gate input (attention over wire1)
- Layer 2: Gather second gate input (attention over wire2)
- Layer 3: Compute gate function (FFN, no attention needed)
- Layer 4: Update wiring for next iteration

This clean separation — two gather layers, one compute layer, one update layer
— directly mirrors the structure of the Lean formalization in ProgramEncoding.lean,
where phase1Wiring, DNF circuit computation, and phase3Wiring correspond
directly to layers 1-2, 3, and 4.

---

## Open Questions Raised by This Work

**Statistical learnability.** Wei et al. prove SM approximation for their
construction. An important open question is whether the 4-layer agent construction
also admits SM approximation — whether the specific weights realizing circuit
simulation can be learned from polynomial samples. The bounded precision of the
Coppola construction makes this more plausible than for Pérez et al.

**Belief propagation simulation.** Section 8.3 of Coppola (2026) conjectures
that a transformer agent can simulate one step of belief propagation over a
Logical Bayesian Network factor graph. This would close the loop between the
three characteristica universalis papers: the QBBN inference engine (Coppola
2024), the statistical parsing system (Coppola 2026a), and the universality
proof (Coppola 2026b).

**Optimal depth.** The paper notes that 4 layers may not be minimal. A 2-layer
construction (one gather layer with two heads, one compute layer) may suffice.

**Trained transformers.** Do trained transformers learn weight configurations
that approximate the circuit simulation structure? Mechanistic interpretability
evidence is suggestive. This is the empirical counterpart to the theoretical
construction.

**Lean formalization completeness.** The UniversalLean repository formalizes
the core construction. Completing the formalization — particularly the
MainTheorems.lean file with full proofs of Theorems 5.1 and 5.2 — would make
this the first formally verified Turing completeness proof for transformer agents.