import UniversalLean.AgentCompleteness.TuringMachine
import UniversalLean.AgentCompleteness.Layers
import UniversalLean.AgentCompleteness.Binary

namespace AgentCompleteness

def tmTokenCount (tapeLen k : ℕ) : ℕ :=
  tapeLen + bitWidth tapeLen + bitWidth k

def trivialProgram (n depth : ℕ) : Program n depth :=
  fun _layer j => { wire1 := j, wire2 := j }

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

def encode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (cfg : TMConfig k tapeLen) :
    CircuitState (tmTokenCount tapeLen k) depth :=
  fun i =>
    let n    := tmTokenCount tapeLen k
    let hw   := bitWidth tapeLen
    let sw   := bitWidth k
    let prog := trivialProgram n depth
    if ht : i.val < tapeLen then
      defaultToken i (cfg.tape ⟨i.val, ht⟩) hd prog
    else if hh : i.val < tapeLen + hw then
      let bitIdx : Fin hw := ⟨i.val - tapeLen, by omega⟩
      defaultToken i (natToBits cfg.head.val hw bitIdx) hd prog
    else
      let bitIdx : Fin sw := ⟨i.val - (tapeLen + hw), by simp [tmTokenCount] at i; omega⟩
      defaultToken i (natToBits cfg.state.val sw bitIdx) hd prog

def decodeTape {depth tapeLen k : ℕ}
    (state : CircuitState (tmTokenCount tapeLen k) depth) :
    Fin tapeLen → Bool :=
  fun i =>
    let j : Fin (tmTokenCount tapeLen k) :=
      ⟨i.val, by simp [tmTokenCount]; omega⟩
    (state j).val

def decodeHead {depth tapeLen k : ℕ}
    (state : CircuitState (tmTokenCount tapeLen k) depth)
    (h : bitsToNat (bitWidth tapeLen)
      (fun b => (state ⟨tapeLen + b.val, by simp [tmTokenCount]; omega⟩).val) < tapeLen) :
    Fin tapeLen :=
  ⟨bitsToNat (bitWidth tapeLen)
    (fun b => (state ⟨tapeLen + b.val, by simp [tmTokenCount]; omega⟩).val), h⟩

def decodeState {depth tapeLen k : ℕ}
    (state : CircuitState (tmTokenCount tapeLen k) depth)
    (h : bitsToNat (bitWidth k)
      (fun b => (state ⟨tapeLen + bitWidth tapeLen + b.val,
        by simp [tmTokenCount]; omega⟩).val) < k) :
    Fin k :=
  ⟨bitsToNat (bitWidth k)
    (fun b => (state ⟨tapeLen + bitWidth tapeLen + b.val,
      by simp [tmTokenCount]; omega⟩).val), h⟩

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

lemma decode_tape_encode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (cfg : TMConfig k tapeLen) :
    decodeTape (encode hk hd cfg) = cfg.tape := by
  funext i
  simp [decodeTape, encode, defaultToken, tmTokenCount]
  exact i.isLt

lemma decode_head_encode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (cfg : TMConfig k tapeLen)
    (h : bitsToNat (bitWidth tapeLen)
      (fun b => (encode hk hd cfg
        ⟨tapeLen + b.val, by simp [tmTokenCount]; omega⟩).val) < tapeLen) :
    decodeHead (encode hk hd cfg) h = cfg.head := by
  simp [decodeHead, encode, defaultToken]
  apply Fin.ext
  exact bitsToNat_natToBits (bitWidth tapeLen) cfg.head.val
    (bitWidth_spec cfg.head.val (Nat.pos_of_ne_zero (by omega)))

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
  exact bitsToNat_natToBits (bitWidth k) cfg.state.val
    (bitWidth_spec cfg.state.val (Nat.pos_of_ne_zero (by omega)))

end AgentCompleteness