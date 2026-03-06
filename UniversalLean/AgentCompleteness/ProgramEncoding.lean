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

-- What a well-formed circuit state looks like:
-- tape tokens have COPY gate and self-wiring
-- workspace tokens have the right gate for DNF computation
structure WellFormed {k tapeLen depth : ℕ}
    (hk : 0 < k) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth) : Prop where
  -- tape tokens
  tape_gate : ∀ i : Fin tapeLen,
    (state ⟨i.val, by simp [fullTokenCount, tmTokenCount,
      tmCircuitSize]; omega⟩).gate = GateType.COPY
  tape_wire1 : ∀ i : Fin tapeLen,
    (state ⟨i.val, by simp [fullTokenCount, tmTokenCount,
      tmCircuitSize]; omega⟩).wire1 =
    ⟨i.val, by simp [fullTokenCount, tmTokenCount,
      tmCircuitSize]; omega⟩
  tape_wire2 : ∀ i : Fin tapeLen,
    (state ⟨i.val, by simp [fullTokenCount, tmTokenCount,
      tmCircuitSize]; omega⟩).wire2 =
    ⟨i.val, by simp [fullTokenCount, tmTokenCount,
      tmCircuitSize]; omega⟩
  -- tape values match cfg
  tape_val : ∀ i : Fin tapeLen,
    (state ⟨i.val, by simp [fullTokenCount, tmTokenCount,
      tmCircuitSize]; omega⟩).val = cfg.tape i
  -- state bits match cfg
  state_val : ∀ i : Fin (bitWidth k),
    (state ⟨tapeLen + bitWidth tapeLen + i.val,
      by simp [fullTokenCount, tmTokenCount,
        tmCircuitSize]; omega⟩).val =
    natToBits cfg.state.val (bitWidth k) i

-- encode produces a well-formed state
lemma encode_wellformed {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen) :
    WellFormed hk hL δ cfg (encode hk hd cfg) := by
  constructor
  · intro i
    simp [encode, defaultToken, tmTokenCount]
    exact i.isLt
  · intro i
    simp [encode, defaultToken, tmTokenCount]
    exact i.isLt
  · intro i
    simp [encode, defaultToken, tmTokenCount]
    exact i.isLt
  · intro i
    simp [encode, defaultToken, tmTokenCount, decodeTape]
    exact i.isLt
  · intro i
    simp [encode, defaultToken, tmTokenCount]
    constructor
    · omega
    · constructor
      · have := i.isLt
        simp [bitWidth] at this ⊢
        omega
      · rfl

-- COPY gate with self-wiring preserves val through computeGate
lemma copy_gate_preserves_val {n depth : ℕ}
    (state : CircuitState n depth) (j : Fin n)
    (hgate : (state j).gate = GateType.COPY)
    (hwire1 : (state j).wire1 = j)
    (hwire2 : (state j).wire2 = j) :
    (computeGate (gatherSecondInput
      (gatherFirstInput state)) j).val =
    (state j).val := by
  simp [computeGate, gatherSecondInput, gatherFirstInput,
        applyGate, hgate, hwire1, hwire2]

-- After gather, workspace input tokens hold correct input bits
lemma workspace_inputs_after_gather {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state) :
    ∀ i : Fin (tmInputWidth k),
      let wsStart := tmTokenCount tapeLen k
      let j : Fin (fullTokenCount tapeLen k) :=
        ⟨wsStart + i.val,
          by simp [fullTokenCount, tmTokenCount,
            tmCircuitSize, tmInputWidth]; omega⟩
      (gatherFirstInput state j).scratch1 =
      tmInputBits cfg.state (cfg.tape cfg.head) i := by
  intro i
  simp [gatherFirstInput, tmInputBits]
  by_cases hi : i.val < bitWidth k
  · -- state bit: wire1 points to state region
    simp [phase1Wiring]
    have h1 : (tmTokenCount tapeLen k + i.val) ≥
              tmTokenCount tapeLen k := by omega
    have h2 : (tmTokenCount tapeLen k + i.val) <
              tmTokenCount tapeLen k + tmInputWidth k := by
      simp [tmInputWidth]; omega
    simp [h1, h2, hi]
    have := hwf.state_val ⟨i.val, hi⟩
    simp at this ⊢
    convert this using 2
    simp [fullTokenCount, tmTokenCount, tmCircuitSize]
    omega
  · -- symbol bit: wire1 points to tape at head
    simp [phase1Wiring]
    have h1 : (tmTokenCount tapeLen k + i.val) ≥
              tmTokenCount tapeLen k := by omega
    have h2 : (tmTokenCount tapeLen k + i.val) <
              tmTokenCount tapeLen k + tmInputWidth k := by
      simp [tmInputWidth]; omega
    have hi' : ¬ (i.val < bitWidth k) := hi
    simp [h1, h2, hi']
    have := hwf.tape_val cfg.head
    simp at this ⊢
    convert this using 2
    simp [fullTokenCount, tmTokenCount, tmCircuitSize]
    omega

-- workspace_output_after_compute:
-- computeGate on workspace output tokens gives correct transition bits
lemma workspace_output_after_compute {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state)
    (hInputs : ∀ i : Fin (tmInputWidth k),
      let wsStart := tmTokenCount tapeLen k
      (gatherFirstInput state
        ⟨wsStart + i.val,
          by simp [fullTokenCount, tmTokenCount,
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
      tmOutputBits (δ cfg.state (cfg.tape cfg.head)).1
        (δ cfg.state (cfg.tape cfg.head)).2.1
        (δ cfg.state (cfg.tape cfg.head)).2.2 i := by
  intro i
  simp [computeGate, gatherSecondInput, gatherFirstInput]
  -- the output token's gate is determined by buildTMCircuitEncoding
  -- its scratch registers hold the input bits from hInputs
  -- applying the gate gives the DNF output
  -- which equals tmOutputBits by buildTMCircuitEncoding_correct
  have hcorrect := buildTMCircuitEncoding_correct hk δ
    cfg.state (cfg.tape cfg.head)
  simp [tmInputBits] at hcorrect
  -- extract the specific output bit
  by_cases hi1 : i.val < bitWidth k
  · -- new state bit
    have := hcorrect.2.2 ⟨i.val, hi1⟩
    simp [buildTMCircuitEncoding, tmTruthTable] at this ⊢
    rw [dnf_correct] at this
    simp [tmOutputBits, hi1]
    convert this using 1
    funext j
    have := hInputs j
    simp at this
    exact this.symm
  · by_cases hi2 : i.val = bitWidth k
    · -- write bit
      have := hcorrect.1
      simp [buildTMCircuitEncoding, tmTruthTable] at this ⊢
      rw [dnf_correct] at this
      simp [tmOutputBits]
      constructor
      · exact Nat.not_lt.mp (Nat.le_of_eq hi2.symm)
      · constructor
        · exact hi2
        · convert this using 1
          funext j
          have := hInputs j
          simp at this
          exact this.symm
    · -- direction bit
      have := hcorrect.2.1
      simp [buildTMCircuitEncoding, tmTruthTable] at this ⊢
      rw [dnf_correct] at this
      simp [tmOutputBits]
      refine ⟨Nat.not_lt.mp (by omega), ?_, ?_⟩
      · intro h; exact absurd h hi2
      · convert this using 1
        funext j
        have := hInputs j
        simp at this
        exact this.symm

-- tape_after_writeback:
-- after updateWiring (phase3), tape holds tmStep output
lemma tape_after_writeback {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state)
    (hOutputs :
      let (newState, writeBit, dir) :=
        δ cfg.state (cfg.tape cfg.head)
      ∀ i : Fin (tmOutputWidth k),
        let outputStart :=
          tmTokenCount tapeLen k + tmInputWidth k
        (computeGate (gatherSecondInput
          (gatherFirstInput state))
          ⟨outputStart + i.val,
            by simp [fullTokenCount, tmTokenCount,
              tmCircuitSize, tmOutputWidth]; omega⟩).val =
        tmOutputBits newState writeBit dir i) :
    ∀ i : Fin tapeLen,
      (updateWiring (computeGate (gatherSecondInput
        (gatherFirstInput state)))
        ⟨i.val, by simp [fullTokenCount, tmTokenCount,
          tmCircuitSize]; omega⟩).val =
      (tmStep δ cfg hL).tape i := by
  intro i
  simp [updateWiring, phase3Wiring, tmStep]
  -- tape tokens (index < tapeLen) are not in the state region
  -- so phase3Wiring gives identity wiring
  have hnotState : ¬ (i.val ≥ tapeLen + bitWidth tapeLen ∧
      i.val < tapeLen + bitWidth tapeLen + bitWidth k) := by
    intro ⟨h1, _⟩; omega
  simp [hnotState]
  -- identity wiring means val comes from computeGate output
  -- tape tokens have COPY gate so val = original tape val
  have hcopy := copy_gate_preserves_val state
    ⟨i.val, by simp [fullTokenCount, tmTokenCount,
      tmCircuitSize]; omega⟩
    (hwf.tape_gate i) (hwf.tape_wire1 i) (hwf.tape_wire2 i)
  -- original tape val = cfg.tape i
  rw [hcopy, hwf.tape_val i]
  -- now handle head position: write bit applies at head
  simp [tmStep]
  by_cases hhead : i = cfg.head
  · -- at head: write the write bit
    subst hhead
    simp
    -- the write bit comes from workspace output token
    have hwrite := hOutputs ⟨bitWidth k,
      by simp [tmOutputWidth]; omega⟩
    simp [tmOutputBits] at hwrite
    simp [hwrite]
  · -- not at head: tape unchanged
    simp [hhead]

-- Main theorem: forwardPass simulates tmStep
theorem forwardPass_simulates_via_program {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state) :
    decodeTape (forwardPass state) =
    (tmStep δ cfg hL).tape := by
  funext i
  simp [decodeTape, forwardPass]
  -- step 1: workspace inputs correct after gather
  have hInputs := workspace_inputs_after_gather
    hk hd hL δ cfg state hwf
  -- step 2: workspace outputs correct after compute
  have hOutputs := workspace_output_after_compute
    hk hd hL δ cfg state hwf hInputs
  -- step 3: tape correct after writeback
  have hFinal := tape_after_writeback
    hk hd hL δ cfg state hwf hOutputs i
  convert hFinal using 1
  simp [updateWiring, computeGate, gatherSecondInput,
        gatherFirstInput, phase3Wiring]

end AgentCompleteness