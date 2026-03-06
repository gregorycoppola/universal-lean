# Review: Giannou et al. (2023) — "Looped Transformers as Programmable Computers"

**Authors:** Angeliki Giannou, Shashank Rajput, Jy-yong Sohn, Kangwook Lee,
Jason D. Lee, Dimitris Papailiopoulos
**Venue:** ICML 2023
**arXiv:** 2301.13196

---

## Summary

Giannou et al. construct explicit looped transformers that simulate
one-instruction-set computers (OISCs). Their primary construction implements
SUBLEQ — subtract and branch if less than or equal to zero — a single
instruction that is itself Turing complete. They show a 9-layer, 2-head
transformer can execute one SUBLEQ instruction per loop iteration, and
extend this to a FLEQ framework requiring up to 9 + max(l_i) layers. They
also demonstrate the construction can execute linear algebra routines,
in-context learning algorithms, and other programs.

The key technical contributions are: (1) encoding program counters in
positional encodings, (2) carrying intermediate state through scratchpad
columns appended to the sequence, (3) implementing binary subtraction via
feedforward layers, and (4) using attention to perform memory read/write
operations indexed by the program counter.

The looped transformer applies the same multi-layer network repeatedly:

    X^(t+1) = TF(W; X^(t))

This is structurally an agent loop — the same network applied iteratively
to an evolving state. However as discussed below, the framing and the
use of the internal mechanisms differ importantly from Coppola (2026).

---

## Do Giannou et al. Use an Agent Loop?

**Partially — but not in the architecturally clean sense of Coppola (2026).**

Giannou et al. do use a loop: the looped transformer applies TF(W; ·)
repeatedly, which is formally the same read-compute-write structure.
This is the closest prior work to Coppola (2026) in terms of the
iteration mechanism.

However, the loop in Giannou et al. is implementing a CPU executing
SUBLEQ instructions. The "state" being read and written is a scratchpad
that encodes program counters, registers, and memory — none of which
correspond to natural transformer representations. The loop is present
but it is in service of emulating a von Neumann architecture, not in
service of a clean separation between bounded computation (transformer)
and unbounded iteration (loop).

In Coppola (2026), the loop is the primary architectural primitive. The
transformer simulates one layer of a Boolean circuit per pass, and the
loop provides depth. The separation is clean and the transformer does
only what transformers naturally do.

---

## Compare and Contrast

### Core Architectural Difference

Both papers use a looped transformer. The difference is what the loop is
doing and whether the transformer components are used naturally.

| Property | Giannou et al. (2023) | Coppola (2026) |
|---|---|---|
| Architecture | Looped transformer (shared weights) | Agent loop (read-compute-write) |
| Iteration | Loop over SUBLEQ instructions | Loop over circuit layers |
| Transformer depth | 9-13 layers | 4 layers |
| Attention role | Memory read/write via PC | Content-addressable lookup |
| FFN role | Binary subtraction, PC update | Gate function computation |
| Proof technique | OISC simulation | Boolean circuit simulation |
| State representation | Scratchpad columns + PC in pos enc | Typed proposition tokens |
| Primary contribution | Explicit programmable construction | Natural primitive identification |

### What Giannou et al. Do Better

**Explicit programmability.** Giannou et al. show the looped transformer
is not just Turing complete in principle but can execute concrete programs:
sorting algorithms, linear algebra, in-context learning. This is a
stronger practical demonstration than a pure Turing completeness proof.

**Detailed construction.** The SUBLEQ construction is fully explicit with
concrete weight matrices given for each layer. This makes it a useful
reference for mechanistic interpretability: you can inspect exactly which
attention heads are doing what at each layer.

**The FLEQ extension.** The generalization beyond SUBLEQ to a broader
instruction set (FLEQ) shows the construction is not a one-trick proof
but a general programming framework for looped transformers.

### What Coppola (2026) Does Better

**Fewer layers.** The SUBLEQ construction requires 9 layers; FLEQ up to
9 + max(l_i). Coppola (2026) requires 4 layers. The reduction comes from
the cleaner proof strategy: circuit simulation requires only gather-gather-
compute-update, whereas SUBLEQ simulation requires decode-fetch-execute-
writeback-branch all within the transformer itself.

**Natural use of attention.** This is the central critique of Giannou et al.
in Coppola (2026). Their attention heads are implementing memory transfer
operations indexed by program counters stored in positional encodings.
This is valid but unnatural — attention was designed for content-addressable
lookup, not PC-indexed memory access.

In Coppola (2026), attention performs exactly content-addressable lookup:
Layer 1 queries wire1 against pos to gather the first gate input, Layer 2
queries wire2 against pos to gather the second. The key-query dot product
is doing what it does in language models — matching content to retrieve
a value. Giannou et al.'s attention is doing something that happens to be
implementable with the attention mechanism but has no relationship to its
design purpose.

**The typed proposition connection.** The circuit state as a knowledge base
of typed propositions connects Coppola (2026) to the characteristica
universalis framework. Each token encodes gate(pos, val, type, in1, in2)
— a fully typed predicate. This interpretation is unavailable in Giannou
et al., where tokens encode scratchpad values and program counters.

**Conceptual clarity of the separation.** In Giannou et al., both the
bounded computation (gate functions) and the control flow (branching,
PC update) live inside the transformer. In Coppola (2026), the transformer
handles only bounded computation; the loop handles control flow and
unbounded iteration. This separation is architecturally honest and maps
directly to how agents are deployed in practice.

### Relationship to the Lean Formalization

The Lean formalization in UniversalLean mirrors the Coppola (2026) structure
exactly. The four-phase structure in ProgramEncoding.lean (load inputs,
compute gates, write back, update wiring) corresponds directly to Layers
1-4 of the paper. A formalization of Giannou et al. would require modeling
the SUBLEQ instruction cycle, binary subtraction in the FFN, and PC-indexed
attention — substantially more complex and less compositional than the
circuit simulation proof.

The TMCorrectness.lean file proves forwardPass_simulates_via_program by
chaining three phase lemmas. The analogous proof for Giannou et al. would
need to chain fetch, decode, execute, writeback, and branch lemmas —
each with more complex invariants because the scratchpad state is
less structured than the typed proposition encoding.

---

## Assessment

Giannou et al. is the most directly comparable prior work to Coppola (2026).
Both use looped transformers; both give explicit constructions rather than
existence proofs. The key differences are layer count (9-13 vs 4),
attention naturalness (PC-indexed memory vs content-addressable lookup),
and conceptual framing (CPU emulation vs circuit simulation over typed
propositions).

Coppola (2026) is a direct response to the question implicit in Giannou
et al.: is there a Turing completeness proof where the transformer computes
naturally? The answer is yes, and the circuit simulation construction
provides it in fewer layers with a cleaner architectural story.

The Giannou et al. construction remains valuable as a demonstration of
explicit programmability. The two papers are complementary: Giannou et al.
show you can run arbitrary programs on a looped transformer; Coppola (2026)
shows the natural computational primitives of attention and FFN are
sufficient for universal computation without reverse-engineering.