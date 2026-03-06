# Encoding.lean — Translating TM Configurations to Circuit States

This file defines how a Turing machine configuration (tape, head position,
machine state) is represented as a transformer CircuitState, and proves
that the encoding and decoding functions are inverses of each other.

This is the formal version of Section 3 of the paper.

## The Layout

A TMConfig with tapeLen tape cells and k machine states is encoded into
a CircuitState with tmTokenCount tapeLen k tokens, laid out as follows:

Tokens 0 .. tapeLen-1: tape cells.
Each token's val field holds the Boolean value of that tape cell.
Gate is COPY, wiring is self. These tokens are the working memory.

Tokens tapeLen .. tapeLen + bitWidth(tapeLen) - 1: head position.
The head position is a natural number less than tapeLen. It is stored
in binary, one bit per token, using natToBits.

Tokens tapeLen + bitWidth(tapeLen) .. tmTokenCount-1: machine state.
The machine state is a natural number less than k. It is stored in
binary, one bit per token, using natToBits.

## Key Definitions

tmTokenCount tapeLen k — Total token count: tapeLen + bitWidth(tapeLen) + bitWidth(k).
This is the width of the transformer when simulating a k-state TM on a
tape of length tapeLen.

defaultToken i v hd prog — Constructs a token at position i with value v,
COPY gate, self-wiring on both wire1 and wire2, and the given program.
This is the template for all tokens in the initial encoding.

encode hk hd cfg — Converts a TMConfig into a CircuitState. For tape region
indices, uses cfg.tape to set val. For head region indices, uses natToBits
on cfg.head.val. For state region indices, uses natToBits on cfg.state.val.
All tokens get defaultToken structure with COPY gate and self-wiring.

decodeTape state — Reads back the tape by extracting val from each token
in the tape region (indices 0 .. tapeLen-1).

decodeHead state h — Reads back the head position by extracting val bits
from the head region and applying bitsToNat. The hypothesis h asserts
the decoded natural number is less than tapeLen, making it a valid Fin.

decodeState state h — Reads back the machine state by extracting val bits
from the state region and applying bitsToNat. The hypothesis h asserts
the decoded value is less than k.

decode hk hd hhead hstate state — Assembles a full TMConfig from a CircuitState
by calling decodeTape, decodeHead, and decodeState.

## Round-Trip Lemmas

decode_tape_encode — decodeTape(encode(cfg)) = cfg.tape. Proved by funext
and unfolding: for index i < tapeLen, encode sets val to cfg.tape[i], and
decodeTape reads val back directly.

decode_head_encode — decodeHead(encode(cfg)) = cfg.head. Proved by Fin.ext
and applying bitsToNat_natToBits: the head region tokens store
natToBits(cfg.head.val, bitWidth(tapeLen)), so bitsToNat recovers cfg.head.val.
This uses the axiom bitsToNat_natToBits with the bound from bitWidth_spec.

decode_state_encode — decodeState(encode(cfg)) = cfg.state. Same argument
as decode_head_encode applied to the state region.

## Why the Round-Trip Matters

The round-trip lemmas establish that encode is a faithful representation:
no information is lost. This is essential for the simulation proof —
we need to know that when we start from encode(cfg) and run the transformer,
the initial tape decoding matches cfg.tape. The lemma encode_wellformed
in ProgramEncoding.lean builds on these round-trips to establish the
full WellFormed invariant for the initial state.