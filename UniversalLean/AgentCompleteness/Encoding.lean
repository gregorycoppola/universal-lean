import UniversalLean.AgentCompleteness.TuringMachine
import UniversalLean.AgentCompleteness.Layers

namespace AgentCompleteness

-- Encoding strategy:
-- We lay out the CircuitState as:
--   tokens 0..tapeLen-1  : tape cells
--   token  tapeLen       : head position
--   token  tapeLen+1     : machine state
--
-- n = tapeLen + 2
-- Each token's val encodes the relevant bit

-- The number of circuit tokens needed for a TM config
def tmTokenCount (tapeLen : ℕ) : ℕ := tapeLen + 2

-- Build a trivial program (identity wiring - each gate reads itself)
-- Real program would encode TM transition function
def trivialProgram (n depth : ℕ) : Program n depth :=
  fun _layer j => { wire1 := j, wire2 := j }

-- Encode a TMConfig into a CircuitState
-- For now: tape bits go into token vals, head/state encoded in last two tokens
def encode {k tapeLen depth : ℕ}
    (hk : 0 < k)
    (hd : 0 < depth)
    (cfg : TMConfig k tapeLen) :
    CircuitState (tmTokenCount tapeLen) depth :=
  fun i =>
    let n := tmTokenCount tapeLen
    let prog := trivialProgram n depth
    let iter0 : Fin depth := ⟨0, hd⟩
    if h : i.val < tapeLen then
      -- tape cell token
      { val      := cfg.tape ⟨i.val, h⟩
        pos      := i
        gate     := GateType.COPY
        wire1    := i
        wire2    := i
        scratch1 := false
        scratch2 := false
        iteration := iter0
        program  := prog }
    else if i.val = tapeLen then
      -- head position token: val = true if head is at position 0 (simplified)
      -- full encoding would use binary representation
      { val      := cfg.head.val == 0
        pos      := i
        gate     := GateType.COPY
        wire1    := i
        wire2    := i
        scratch1 := false
        scratch2 := false
        iteration := iter0
        program  := prog }
    else
      -- machine state token: val = true if in state 0
      { val      := cfg.state.val == 0
        pos      := i
        gate     := GateType.COPY
        wire1    := i
        wire2    := i
        scratch1 := false
        scratch2 := false
        iteration := iter0
        program  := prog }

-- Decode a CircuitState back to tape contents
-- Just reads the val fields of tape tokens
def decodeTape {depth tapeLen : ℕ}
    (state : CircuitState (tmTokenCount tapeLen) depth) :
    Fin tapeLen → Bool :=
  fun i =>
    let j : Fin (tmTokenCount tapeLen) := ⟨i.val, by simp [tmTokenCount]; omega⟩
    (state j).val

-- Decode full TMConfig (sorry'd: head/state decoding needs binary encoding)
def decode {k tapeLen depth : ℕ}
    (hk : 0 < k)
    (state : CircuitState (tmTokenCount tapeLen) depth) :
    TMConfig k tapeLen := by
  sorry

-- Key property: decoding tape after encoding gives back original tape
lemma decode_tape_encode {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (cfg : TMConfig k tapeLen) :
    decodeTape (encode hk hd cfg) = cfg.tape := by
  funext i
  simp [decodeTape, encode, tmTokenCount]
  exact i.isLt

end AgentCompleteness