import UniversalLean.AgentCompleteness.TuringMachine
import UniversalLean.AgentCompleteness.Layers
import UniversalLean.AgentCompleteness.Binary

namespace AgentCompleteness

-- Encoding layout:
-- tokens 0..tapeLen-1          : tape cells (1 bit each)
-- tokens tapeLen..tapeLen+hw-1 : head position (binary, hw bits)
-- tokens tapeLen+hw..n-1       : machine state (binary, sw bits)
--
-- where hw = ceil(log2(tapeLen)), sw = ceil(log2(k))

-- Bit width needed to represent values < n
def bitWidth (n : ℕ) : ℕ := Nat.log2 n + 1

def tmTokenCount (tapeLen k : ℕ) : ℕ :=
  tapeLen + bitWidth tapeLen + bitWidth k

def trivialProgram (n depth : ℕ) : Program n depth :=
  fun _layer j => { wire1 := j, wire2 := j }

-- Helper to build a default token
def defaultToken {n depth : ℕ}
    (i : Fin n) (v : Bool) (hd : 0 < depth) (prog : Program n depth) : Token n depth :=
  { val      := v
    pos      := i
    gate     := GateType.COPY
    wire1    := i
    wire2    := i
    scratch1 := false
    scratch2 := false
    iteration := ⟨0, hd⟩
    program  := prog }

-- Encode a TMConfig into a CircuitState
def encode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (cfg : TMConfig k tapeLen) :
    CircuitState (tmTokenCount tapeLen k) depth :=
  fun i =>
    let n    := tmTokenCount tapeLen k
    let hw   := bitWidth tapeLen
    let sw   := bitWidth k
    let prog := trivialProgram n depth
    -- tape region
    if ht : i.val < tapeLen then
      defaultToken i (cfg.tape ⟨i.val, ht⟩) hd prog
    -- head position region (binary encoded)
    else if hh : i.val < tapeLen + hw then
      let bitIdx : Fin hw := ⟨i.val - tapeLen, by omega⟩
      defaultToken i (natToBits cfg.head.val hw bitIdx) hd prog
    -- machine state region (binary encoded)
    else
      let bitIdx : Fin sw := ⟨i.val - (tapeLen + hw), by simp [tmTokenCount] at i; omega⟩
      defaultToken i (natToBits cfg.state.val sw bitIdx) hd prog

-- Decode tape from CircuitState
def decodeTape {depth tapeLen k : ℕ}
    (state : CircuitState (tmTokenCount tapeLen k) depth) :
    Fin tapeLen → Bool :=
  fun i =>
    let j : Fin (tmTokenCount tapeLen k) :=
      ⟨i.val, by simp [tmTokenCount]; omega⟩
    (state j).val

-- Decode head position from CircuitState
def decodeHead {depth tapeLen k : ℕ}
    (state : CircuitState (tmTokenCount tapeLen k) depth)
    (h : bitsToNat (bitWidth tapeLen)
      (fun b => (state ⟨tapeLen + b.val, by simp [tmTokenCount]; omega⟩).val) < tapeLen) :
    Fin tapeLen :=
  ⟨bitsToNat (bitWidth tapeLen)
    (fun b => (state ⟨tapeLen + b.val, by simp [tmTokenCount]; omega⟩).val), h⟩

-- Decode machine state from CircuitState
def decodeState {depth tapeLen k : ℕ}
    (state : CircuitState (tmTokenCount tapeLen k) depth)
    (h : bitsToNat (bitWidth k)
      (fun b => (state ⟨tapeLen + bitWidth tapeLen + b.val,
        by simp [tmTokenCount]; omega⟩).val) < k) :
    Fin k :=
  ⟨bitsToNat (bitWidth k)
    (fun b => (state ⟨tapeLen + bitWidth tapeLen + b.val,
      by simp [tmTokenCount]; omega⟩).val), h⟩

-- Decode full TMConfig
def decode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (hhead : ∀ (state : CircuitState (tmTokenCount tapeLen k) depth),
      bitsToNat (bitWidth tapeLen)
        (fun b => (state ⟨tapeLen + b.val, by simp [tmTokenCount]; omega⟩).val) < tapeLen)
    (hstate : ∀ (state : CircuitState (tmTokenCount tapeLen k) depth),
      bitsToNat (bitWidth k)
        (fun b => (state ⟨tapeLen + bitWidth tapeLen + b.val,
          by simp [tmTokenCount]; omega⟩).val) < k)
    (state : CircuitState (tmTokenCount tapeLen k) depth) :
    TMConfig k tapeLen :=
  { tape  := decodeTape state
    head  := decodeHead state (hhead state)
    state := decodeState state (hstate state) }

-- Key lemma: tape round trips through encode/decode
lemma decode_tape_encode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (cfg : TMConfig k tapeLen) :
    decodeTape (encode hk hd cfg) = cfg.tape := by
  funext i
  simp [decodeTape, encode, defaultToken, tmTokenCount]
  exact i.isLt

-- Key lemma: head round trips (sorry'd: needs bitsToNat_natToBits)
lemma decode_head_encode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (cfg : TMConfig k tapeLen)
    (h : bitsToNat (bitWidth tapeLen)
      (fun b => (encode hk hd cfg
        ⟨tapeLen + b.val, by simp [tmTokenCount]; omega⟩).val) < tapeLen) :
    decodeHead (encode hk hd cfg) h = cfg.head := by
  simp [decodeHead, encode, defaultToken]
  apply Fin.ext
  sorry

-- Key lemma: state round trips (sorry'd: needs bitsToNat_natToBits)
lemma decode_state_encode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (cfg : TMConfig k tapeLen)
    (h : bitsToNat (bitWidth k)
      (fun b => (encode hk hd cfg
        ⟨tapeLen + bitWidth tapeLen + b.val,
          by simp [tmTokenCount]; omega⟩).val) < k) :
    decodeState (encode hk hd cfg) h = cfg.state := by
  simp [decodeState, encode, defaultToken]
  apply Fin.ext
  sorry

end AgentCompleteness