# Review: Pérez, Barceló & Marinkovic (2021) — "Attention is Turing Complete"

**Authors:** Jorge Pérez, Pablo Barceló, Javier Marinkovic (Universidad de Chile /
Universidad Católica de Chile)
**Venue:** JMLR 22 (2021) — originally ICLR 2019
**arXiv:** 1901.03429

---

## Summary

Pérez et al. prove that the Transformer architecture with hard attention and
arbitrary-precision positional encodings is Turing complete. Their main result
(Theorem 6) constructs a Transformer TransM that simulates any Turing machine M:
a single encoder layer plus three decoder layers suffices, with positional encodings
using values 1/i and 1/i^2 to enable position-indexed lookup.

The construction is a direct TM simulation. The encoder embeds the input string
with positional information. The decoder builds up the computation history
autoregressively: each output vector y_i encodes the TM state q^(i) and the
symbol under the head s^(i) at step i. Three decoder layers handle: (1) applying
the transition function delta via a two-layer FFN (Lemma 8), (2) computing the
current head position c^(i) as a cumulative sum of movement directions via
uniform attention (Lemma 9), and (3) finding the last time the head visited the
current cell — the index ell(i) — via a clever scoring function that minimizes
|<q, k>| rather than maximizing it (Lemma 10).

The paper also proves important negative results: without positional encodings,
Transformers satisfy a proportion invariance property that prevents them from
recognizing even basic regular languages (Proposition 3). With fixed precision,
positional encodings reduce to a finite alphabet extension, so fixed-precision
Transformers are not Turing complete. Arbitrary precision is essential.

---

## Do Pérez et al. Use an Agent Loop?

**No — and this is the most fundamental difference from Coppola (2026).**

Pérez et al. use an autoregressive decoder that generates the computation history
one token at a time. Each decoder step produces y_{r+1} from (y_0, ..., y_r).
The unbounded computation comes from running the decoder for arbitrarily many
steps r, producing a sequence of length T where T is the TM's computation time.

There is no external loop in any architectural sense. The "iteration" is the
sequential decoder generation process — the same mechanism used for language
modeling. The transformer grows with the computation: to simulate T steps of
a TM you need T decoder outputs, and the attention over past decoder states
grows in cost as O(T^2).

More critically, the construction requires **arbitrary precision** in the
positional encodings. The values 1/i and 1/i^2 are used to locate the last
visit to a tape cell (Lemma 10 uses the scoring function minimizing |<q,k>|
to find the maximum j such that c^(j) = c^(i+1)). This requires unbounded
precision as i grows — the differences between 1/i and 1/(i+1) become
arbitrarily small. Pérez et al. acknowledge explicitly that fixed-precision
Transformers are NOT Turing complete under their framework.

By contrast, Coppola (2026) uses a **constant-depth 4-layer transformer** in
an explicit read-compute-write agent loop with precision only O(log n) —
bounded and finite, independent of computation time.

---

## Compare and Contrast

### Core Architectural Difference

Pérez et al. encode the entire computation history inside the growing decoder
sequence, using arbitrary-precision positional encodings to index into it.
Coppola (2026) uses a constant transformer over external state, with the agent
loop providing unbounded computation and binary positional encodings providing
bounded precision.

| Property | Pérez et al. (2021) | Coppola (2026) |
|---|---|---|
| Architecture | Encoder + 3-layer decoder | 4-layer encoder-style transformer |
| Iteration | Autoregressive decoder (length T) | Explicit agent loop |
| Transformer depth | 1 encoder + 3 decoder layers | 4 layers — constant |
| Precision | Arbitrary (1/i, 1/i^2) — unbounded | O(log n) — bounded |
| Attention role | Position lookup via 1/i encodings | Content-addressable lookup |
| FFN role | Transition function delta | Gate function computation |
| Proof technique | Direct TM simulation | Boolean circuit simulation |
| Fixed precision? | NOT Turing complete | Turing complete |
| Primary contribution | First TC proof for Transformers | Natural + agent framing |

### What Pérez et al. Do Better

**Historical priority.** This is the founding paper for transformer Turing
completeness. The result that attention alone (without recurrence) suffices for
universal computation was genuinely surprising in 2019 and opened the entire
line of research that Giannou, Wei, and Coppola follow.

**Elegance of the decoder construction.** The three-layer decoder is conceptually
clean. Lemma 8 (FFN simulates delta) is the natural observation that a lookup
table over finite (state, symbol) pairs is implementable by a two-layer network.
Lemma 9 (uniform attention computes cumulative sum of movements = head position)
is beautiful: setting all keys to zero forces uniform attention, so the average
of the movement values gives the cumulative sum. Lemma 10 (hard attention finds
the last visit to a cell) is the most technically inventive step.

**The proportion invariance result.** The negative result in Section 3 — that
Transformers without positional encodings satisfy proportion invariance and
cannot recognize even (ab)* — is a clean and important limitation result that
remains useful for understanding transformer expressivity.

**Minimal architecture.** 1 encoder layer + 3 decoder layers is a very small
transformer. The paper identifies precisely which components are needed.

### What Coppola (2026) Does Better

**Bounded precision.** This is arguably the most important practical distinction.
Pérez et al. explicitly acknowledge their construction does not work with fixed
precision. Coppola (2026) requires only O(log n) bits — the binary positional
encoding of gate indices — which is finite and bounded by the circuit size, not
by the computation time. A real transformer could in principle implement the
Coppola construction with finite-precision arithmetic.

**The agent loop as the right model.** Pérez et al. prove Turing completeness
of a transformer that generates a length-T sequence to simulate T steps of a TM.
This is not how AI agents work in practice. Coppola (2026) proves Turing
completeness of a constant transformer in a read-compute-write loop — which is
exactly how tool-calling LLMs, autonomous agents, and agentic AI systems are
deployed. The architectural model is honest.

**Constant depth independent of computation.** In Pérez et al., the decoder
must run for T steps, and each step attends over all previous steps — O(T^2)
total attention computation. In Coppola (2026), each forward pass is O(n^2)
in the circuit width n, independent of how many passes have been run. The
transformer never grows.

**Natural use of attention.** Pérez et al.'s attention in Lemma 10 uses the
scoring function phi(x) = -|x|, minimizing the absolute dot product to find
position matches via 1/i encodings. This is a clever mathematical trick but
has no relationship to how attention operates in trained transformers. Coppola
(2026) uses standard dot-product attention for content-addressable lookup of
gate inputs — the mechanism that operates in language models when retrieving
relevant tokens.

**Fewer layers.** 4 layers vs. 1 + 3 = 4 layers is actually the same count,
but the 4 Coppola layers each have a single clear purpose (gather input 1,
gather input 2, compute gate, update wiring) whereas the Pérez decoder layers
entangle transition computation, position computation, and symbol lookup in a
less separable way.

**Connection to the characteristica universalis.** Pérez et al. have no
conceptual framework connecting their construction to formal logic or knowledge
representation. The circuit state as typed propositions, with attention as
universal instantiation and FFN as modus ponens, is unique to Coppola (2026)
and provides a principled account of why transformers compute naturally.

### Relationship to the Lean Formalization

The Lean formalization in UniversalLean is structurally incompatible with a
direct formalization of Pérez et al. The Pérez construction requires:

- Arbitrary-precision rational arithmetic (the 1/i, 1/i^2 encodings)
- A growing decoder sequence modeled as a list of length T
- The scoring function phi(x) = -|x| which is non-standard
- Lemma 10's subtle argument about minimizing |<q,k>| to find argmax over
  cell visits — which requires reasoning about real-valued inequalities

The Coppola construction uses only:

- Binary (Boolean) values for circuit state
- Fixed-length sequences of typed proposition tokens
- Standard dot-product attention with softmax concentration
- Boolean gate functions implementable with O(1) ReLU neurons

The TuringMachine.lean model in UniversalLean uses Fin k for states and
Fin tapeLen for head position — finite types with automatic bounds checking.
This matches the Coppola construction directly. A formalization of Pérez et al.
would require real-valued arithmetic and unbounded sequences, making it a
substantially harder Lean target and one where the type system provides less
automatic proof assistance.

---

## Assessment

Pérez et al. is the foundational paper in this area and deserves full credit for
establishing that transformers are Turing complete based on their intrinsic
computational mechanism rather than by definition (as in Neural Turing Machines).
The three-layer decoder construction is elegant and the proportion invariance
negative result is important.

However the construction has two significant limitations from the perspective of
Coppola (2026): it requires arbitrary precision (making it physically unrealizable
with finite-precision hardware) and it does not correspond to the agent loop
model of how transformers are deployed in practice.

Coppola (2026) can be understood as answering the question: can we have Turing
completeness with (a) bounded precision, (b) an explicit agent loop, and (c)
attention doing what attention actually does? The answer is yes, in 4 layers,
via Boolean circuit simulation over typed propositions.

The four papers together — Pérez, Giannou, Wei, Coppola — form a natural
progression: existence proof (Pérez) → explicit programmable construction
(Giannou) → statistical learnability (Wei) → natural primitives + agent loop
+ bounded precision (Coppola).