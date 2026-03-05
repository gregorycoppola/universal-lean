import UniversalLean.AgentCompleteness.FiniteCircuit
import UniversalLean.AgentCompleteness.Layers

namespace AgentCompleteness

def tmCircuitSize (k : ℕ) : ℕ :=
  tmInputWidth k + tmOutputWidth k

def fullTokenCount (tapeLen k : ℕ) : ℕ :=
  tmTokenCount tapeLen k + tmCircuitSize k

def phase1Wiring (tapeLen k : ℕ) :
    Fin (fullTokenCount tapeLen k) →
    GateWiring (fullTokenCount tapeLen k) :=
  fun i =>
    let n := fullTokenCount tapeLen k
    let workspaceStart := tmTokenCount tapeLen k
    if h : i.val ≥ workspaceStart ∧
           i.val < workspaceStart + tmInputWidth k then
      let inputIdx := i.val - workspaceStart
      if inputIdx < bitWidth k then
        { wire1 := ⟨tapeLen + bitWidth tapeLen + inputIdx,
            by simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega⟩
          wire2 := ⟨tapeLen + bitWidth tapeLen + inputIdx,
            by simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega⟩ }
      else
        { wire1 := ⟨0, by simp [fullTokenCount, tmTokenCount,
            tmCircuitSize]; omega⟩
          wire2 := ⟨0, by simp [fullTokenCount, tmTokenCount,
            tmCircuitSize]; omega⟩ }
    else
      { wire1 := ⟨i.val % n, Nat.mod_lt _ (by
          simp [fullTokenCount, tmTokenCount, tmCircuitSize]
          omega)⟩
        wire2 := ⟨i.val % n, Nat.mod_lt _ (by
          simp [fullTokenCount, tmTokenCount, tmCircuitSize]
          omega)⟩ }

def phase3Wiring (tapeLen k : ℕ) :
    Fin (fullTokenCount tapeLen k) →
    GateWiring (fullTokenCount tapeLen k) :=
  fun i =>
    let n := fullTokenCount tapeLen k
    let workspaceStart := tmTokenCount tapeLen k
    let outputStart := workspaceStart + tmInputWidth k
    if h : i.val ≥ tapeLen + bitWidth tapeLen ∧
           i.val < tapeLen + bitWidth tapeLen + bitWidth k then
      let bitIdx := i.val - (tapeLen + bitWidth tapeLen)
      { wire1 := ⟨outputStart + bitIdx,
          by simp [fullTokenCount, tmTokenCount, tmCircuitSize,
                   tmOutputWidth]; omega⟩
        wire2 := ⟨outputStart + bitIdx,
          by simp [fullTokenCount, tmTokenCount, tmCircuitSize,
                   tmOutputWidth]; omega⟩ }
    else
      { wire1 := ⟨i.val % n, Nat.mod_lt _ (by
          simp [fullTokenCount, tmTokenCount, tmCircuitSize]
          omega)⟩
        wire2 := ⟨i.val % n, Nat.mod_lt _ (by
          simp [fullTokenCount, tmTokenCount, tmCircuitSize]
          omega)⟩ }

def buildProgram {k tapeLen : ℕ} (hk : 0 < k)
    (δ : TMTransition k)
    (depth : ℕ) (hd : 0 < depth) :
    Program (fullTokenCount tapeLen k) depth :=
  fun layer j =>
    if layer.val = 0 then
      { wire1 := j, wire2 := j }
    else if layer.val = 1 then
      phase1Wiring tapeLen k j
    else
      phase3Wiring tapeLen k j

def buildTransitionCircuit {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (δ : TMTransition k) :
    Program (fullTokenCount tapeLen k) depth :=
  buildProgram hk δ depth hd

-- Phase 1 correctness:
-- after gather, workspace holds state bits and tape symbol
lemma phase1_correct {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (henc : decodeTape state = cfg.tape) :
    -- after gatherFirstInput, workspace state bits are correct
    ∀ (i : Fin (bitWidth k)),
      let workspaceStart := tmTokenCount tapeLen k
      let j : Fin (fullTokenCount tapeLen k) :=
        ⟨workspaceStart + i.val,
          by simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega⟩
      (gatherFirstInput state j).scratch1 =
      natToBits cfg.state.val (bitWidth k) i := by
  intro i
  simp [gatherFirstInput]
  sorry

-- Phase 3 correctness:
-- after writeback, state region holds new state bits
lemma phase3_correct {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (newState : Fin k) (writeBit : Bool) (dir : Dir)
    (hδ : δ cfg.state (cfg.tape cfg.head) = (newState, writeBit, dir))
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    -- workspace holds correct output bits
    (hWorkspace : ∀ (i : Fin (tmOutputWidth k)),
      let outputStart := tmTokenCount tapeLen k + tmInputWidth k
      let j : Fin (fullTokenCount tapeLen k) :=
        ⟨outputStart + i.val,
          by simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega⟩
      (state j).val = tmOutputBits newState writeBit dir i) :
    -- after phase3, state region is updated correctly
    ∀ (i : Fin (bitWidth k)),
      let stateStart := tapeLen + bitWidth tapeLen
      let j : Fin (fullTokenCount tapeLen k) :=
        ⟨stateStart + i.val,
          by simp [fullTokenCount, tmTokenCount, tmCircuitSize,
                   tmTokenCount]; omega⟩
      (updateWiring state j).val =
      natToBits newState.val (bitWidth k) i := by
  intro i
  simp [updateWiring, phase3Wiring]
  sorry

-- Main theorem: forwardPass with buildTransitionCircuit
-- simulates one TM step
theorem forwardPass_simulates_via_program {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (henc : decodeTape state = cfg.tape) :
    decodeTape (forwardPass state) =
    (tmStep δ cfg hL).tape := by
  simp [forwardPass, tmStep]
  funext i
  simp [decodeTape, updateWiring, computeGate,
        gatherSecondInput, gatherFirstInput]
  -- the tape region tokens read from themselves
  -- so val is preserved from computeGate output
  -- which reads scratch1/scratch2 set by gather
  -- which came from the correct positions
  sorry

end AgentCompleteness