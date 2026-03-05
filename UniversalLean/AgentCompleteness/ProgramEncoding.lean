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
          simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega)⟩
        wire2 := ⟨i.val % n, Nat.mod_lt _ (by
          simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega)⟩ }

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
          simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega)⟩
        wire2 := ⟨i.val % n, Nat.mod_lt _ (by
          simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega)⟩ }

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

-- Helper: tape tokens have COPY gate and self-wiring
-- so computeGate preserves their val
lemma tape_token_copy {n depth : ℕ}
    (state : CircuitState n depth) (j : Fin n)
    (hgate : (state j).gate = GateType.COPY)
    (hwire : (state j).wire1 = j) :
    (computeGate (gatherSecondInput
      (gatherFirstInput state)) j).val =
    (state j).val := by
  simp [computeGate, gatherSecondInput,
        gatherFirstInput, applyGate]
  rw [hgate]
  simp [applyGate]
  -- scratch1 = val of wire1 = val of j = (state j).val
  rw [hwire]

-- Helper: workspace input tokens after gather
-- hold the correct state/symbol bits
lemma workspace_after_gather {k tapeLen depth : ℕ}
    (hk : 0 < k) (hL : 0 < tapeLen)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (henc : ∀ i : Fin tapeLen,
      (state ⟨i.val, by simp [fullTokenCount,
        tmTokenCount, tmCircuitSize]; omega⟩).val =
      cfg.tape i)
    (hstate : ∀ i : Fin (bitWidth k),
      (state ⟨tapeLen + bitWidth tapeLen + i.val,
        by simp [fullTokenCount, tmTokenCount,
          tmCircuitSize]; omega⟩).val =
      natToBits cfg.state.val (bitWidth k) i) :
    -- after gather, workspace input bits hold
    -- state bits and tape symbol
    ∀ i : Fin (tmInputWidth k),
      let ws := tapeLen + bitWidth tapeLen + bitWidth k
      let j : Fin (fullTokenCount tapeLen k) :=
        ⟨ws + i.val,
          by simp [fullTokenCount, tmTokenCount,
            tmCircuitSize, tmInputWidth]; omega⟩
      (gatherFirstInput state j).scratch1 =
      tmInputBits cfg.state (cfg.tape cfg.head) i := by
  intro i
  simp [gatherFirstInput, tmInputBits, phase1Wiring]
  by_cases hi : i.val < bitWidth k
  · -- state bit
    have := hstate ⟨i.val, hi⟩
    simp at this ⊢
    convert this using 2
    simp [fullTokenCount, tmTokenCount, tmCircuitSize]
    omega
  · -- symbol bit
    have hhead := henc cfg.head
    simp at hhead ⊢
    convert hhead using 2
    simp [fullTokenCount, tmTokenCount, tmCircuitSize,
          tmInputWidth] at *
    omega

-- Helper: after computeGate, workspace output tokens
-- hold the correct transition output bits
lemma workspace_output_after_compute {k tapeLen depth : ℕ}
    (hk : 0 < k) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hInputs : ∀ i : Fin (tmInputWidth k),
      let ws := tapeLen + bitWidth tapeLen + bitWidth k
      (gatherFirstInput state
        ⟨ws + i.val, by simp [fullTokenCount, tmTokenCount,
          tmCircuitSize, tmInputWidth]; omega⟩).scratch1 =
      tmInputBits cfg.state (cfg.tape cfg.head) i) :
    let (newState, writeBit, dir) := δ cfg.state (cfg.tape cfg.head)
    ∀ i : Fin (tmOutputWidth k),
      let outputStart := tmTokenCount tapeLen k + tmInputWidth k
      let j : Fin (fullTokenCount tapeLen k) :=
        ⟨outputStart + i.val,
          by simp [fullTokenCount, tmTokenCount,
            tmCircuitSize, tmOutputWidth]; omega⟩
      (computeGate (gatherSecondInput
        (gatherFirstInput state)) j).val =
      tmOutputBits newState writeBit dir i := by
  intro i
  simp [computeGate, gatherSecondInput, gatherFirstInput]
  -- output tokens apply DNF gate to input bits
  -- which by buildTMCircuitEncoding_correct gives
  -- the correct transition output
  sorry

-- Helper: after updateWiring (phase3),
-- tape region holds tmStep output
lemma tape_after_writeback {k tapeLen depth : ℕ}
    (hk : 0 < k) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hOutputs : let (newState, writeBit, dir) :=
        δ cfg.state (cfg.tape cfg.head)
      ∀ i : Fin (tmOutputWidth k),
        let outputStart :=
          tmTokenCount tapeLen k + tmInputWidth k
        let j : Fin (fullTokenCount tapeLen k) :=
          ⟨outputStart + i.val,
            by simp [fullTokenCount, tmTokenCount,
              tmCircuitSize, tmOutputWidth]; omega⟩
        (state j).val =
        tmOutputBits newState writeBit dir i) :
    ∀ i : Fin tapeLen,
      (updateWiring state
        ⟨i.val, by simp [fullTokenCount, tmTokenCount,
          tmCircuitSize]; omega⟩).val =
      (tmStep δ cfg hL).tape i := by
  intro i
  simp [updateWiring, tmStep, phase3Wiring]
  -- tape tokens wire to themselves in phase3
  -- so val is preserved from computeGate output
  -- which for tape cells = original tape value
  -- except at head position where writeBit applies
  sorry

-- Main theorem: forwardPass simulates tmStep
theorem forwardPass_simulates_via_program {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (henc : decodeTape state = cfg.tape)
    (hstate : ∀ i : Fin (bitWidth k),
      (state ⟨tapeLen + bitWidth tapeLen + i.val,
        by simp [fullTokenCount, tmTokenCount,
          tmCircuitSize]; omega⟩).val =
      natToBits cfg.state.val (bitWidth k) i) :
    decodeTape (forwardPass state) =
    (tmStep δ cfg hL).tape := by
  funext i
  simp [decodeTape, forwardPass]
  -- step 1: show workspace inputs are correct after gather
  have hInputs := workspace_after_gather hk hL cfg state
    (fun i => by
      have := congr_fun henc i
      simp [decodeTape] at this
      convert this using 2
      simp [fullTokenCount, tmTokenCount, tmCircuitSize]
      omega)
    hstate
  -- step 2: show workspace outputs are correct after compute
  have hOutputs := workspace_output_after_compute
    hk hL δ cfg state hInputs
  -- step 3: show tape is correct after writeback
  apply tape_after_writeback hk hL δ cfg _ hOutputs i

end AgentCompleteness