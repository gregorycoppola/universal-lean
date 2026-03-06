import UniversalLean.AgentCompleteness.ProgramEncoding

namespace AgentCompleteness

theorem forwardPass_simulates_tmStep {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state) :
    decodeTape (forwardPass state) =
    (tmStep δ cfg hL).tape :=
  forwardPass_simulates_via_program hk hd hL δ cfg state hwf

-- gate field is never modified by any layer
lemma gate_preserved {n depth : ℕ}
    (state : CircuitState n depth) (j : Fin n) :
    (forwardPass state j).gate = (state j).gate := by
  simp [forwardPass, updateWiring, computeGate,
        gatherSecondInput, gatherFirstInput]

-- wire1 after forwardPass comes from program at current iteration
lemma wire1_after_forwardPass {n depth : ℕ}
    (state : CircuitState n depth) (j : Fin n) :
    (forwardPass state j).wire1 =
    (state j).program (state j).iteration j |>.wire1 := by
  simp [forwardPass, updateWiring, computeGate,
        gatherSecondInput, gatherFirstInput]

-- wire2 after forwardPass comes from program at current iteration
lemma wire2_after_forwardPass {n depth : ℕ}
    (state : CircuitState n depth) (j : Fin n) :
    (forwardPass state j).wire2 =
    (state j).program (state j).iteration j |>.wire2 := by
  simp [forwardPass, updateWiring, computeGate,
        gatherSecondInput, gatherFirstInput]

-- For tape tokens, phase3Wiring gives identity so wire1 = j
lemma tape_wire1_preserved {k tapeLen depth : ℕ}
    (hk : 0 < k) (hL : 0 < tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL (fun s b => (⟨0, hk⟩, false, Dir.L)) 
      (⟨⟨0, hk⟩, fun _ => false, ⟨0, hL⟩⟩) state)
    (i : Fin tapeLen) :
    let j : Fin (fullTokenCount tapeLen k) :=
      ⟨i.val, by simp [fullTokenCount, tmTokenCount, tmCircuitSize]; omega⟩
    (forwardPass state j).wire1 = j := by
  simp [wire1_after_forwardPass]
  simp [updateWiring, computeGate, gatherSecondInput,
        gatherFirstInput, phase3Wiring]
  have hnotState : ¬ (i.val ≥ tapeLen + bitWidth tapeLen ∧
      i.val < tapeLen + bitWidth tapeLen + bitWidth k) := by
    intro ⟨h1, _⟩; omega
  simp [hnotState]
  omega

-- State bits after forwardPass match new state from δ
lemma state_bits_after_forwardPass {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state) :
    let (newState, _, _) := δ cfg.state (cfg.tape cfg.head)
    ∀ i : Fin (bitWidth k),
      (forwardPass state
        ⟨tapeLen + bitWidth tapeLen + i.val,
          by simp [fullTokenCount, tmTokenCount,
            tmCircuitSize]; omega⟩).val =
      natToBits newState.val (bitWidth k) i := by
  intro i
  simp [forwardPass, updateWiring, phase3Wiring]
  -- state region tokens are in the phase3 writeback region
  have hInState : (tapeLen + bitWidth tapeLen + i.val) ≥
      tapeLen + bitWidth tapeLen ∧
    (tapeLen + bitWidth tapeLen + i.val) <
      tapeLen + bitWidth tapeLen + bitWidth k := by
    constructor <;> omega
  simp [hInState]
  -- wire1 points to output workspace
  -- which holds the new state bits by workspace_output_after_compute
  have hInputs := workspace_inputs_after_gather hk hd hL δ cfg state hwf
  have hOutputs := workspace_output_after_compute
    hk hd hL δ cfg state hwf hInputs
  have hOut := hOutputs ⟨i.val, by simp [tmOutputWidth]; omega⟩
  simp [tmOutputBits, i.isLt] at hOut
  simp [computeGate, gatherSecondInput, gatherFirstInput] at hOut ⊢
  convert hOut using 2
  simp [fullTokenCount, tmTokenCount, tmCircuitSize, tmOutputWidth,
        tmInputWidth]
  omega

-- Well-formedness is preserved by forwardPass
lemma wellFormed_preserved {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state) :
    WellFormed hk hL δ (tmStep δ cfg hL)
      (forwardPass state) := by
  constructor
  · -- tape_gate: gate field never changes
    intro i
    rw [gate_preserved]
    exact hwf.tape_gate i
  · -- tape_wire1: tape tokens get identity wiring from phase3
    intro i
    simp [wire1_after_forwardPass, updateWiring,
          computeGate, gatherSecondInput, gatherFirstInput,
          phase3Wiring]
    have hnotState : ¬ ((i.val : ℕ) ≥ tapeLen + bitWidth tapeLen ∧
        (i.val : ℕ) < tapeLen + bitWidth tapeLen + bitWidth k) := by
      intro ⟨h1, _⟩; omega
    simp [hnotState]
    apply Fin.ext
    simp
    omega
  · -- tape_wire2: same as wire1
    intro i
    simp [wire2_after_forwardPass, updateWiring,
          computeGate, gatherSecondInput, gatherFirstInput,
          phase3Wiring]
    have hnotState : ¬ ((i.val : ℕ) ≥ tapeLen + bitWidth tapeLen ∧
        (i.val : ℕ) < tapeLen + bitWidth tapeLen + bitWidth k) := by
      intro ⟨h1, _⟩; omega
    simp [hnotState]
    apply Fin.ext
    simp
    omega
  · -- tape_val: follows from tape_after_writeback
    intro i
    have hInputs := workspace_inputs_after_gather hk hd hL δ cfg state hwf
    have hOutputs := workspace_output_after_compute
      hk hd hL δ cfg state hwf hInputs
    have hFinal := tape_after_writeback hk hd hL δ cfg state hwf hOutputs i
    simp [forwardPass]
    convert hFinal using 1
    simp [updateWiring, computeGate, gatherSecondInput,
          gatherFirstInput, phase3Wiring]
    have hnotState : ¬ ((i.val : ℕ) ≥ tapeLen + bitWidth tapeLen ∧
        (i.val : ℕ) < tapeLen + bitWidth tapeLen + bitWidth k) := by
      intro ⟨h1, _⟩; omega
    simp [hnotState]
  · -- state_val: follows from state_bits_after_forwardPass
    intro i
    exact state_bits_after_forwardPass hk hd hL δ cfg state hwf i

-- Iterated stepping
theorem forwardPass_iter_simulates_tmRun {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state₀ : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state₀)
    (d : ℕ) :
    decodeTape (forwardPass^[d] state₀) =
    (tmRun δ cfg d hL).tape := by
  induction d generalizing cfg state₀ with
  | zero =>
    simp [tmRun]
    funext i
    simp [decodeTape]
    exact hwf.tape_val i
  | succ d ih =>
    rw [Function.iterate_succ', Function.comp, tmRun]
    apply ih (tmStep δ cfg hL) (forwardPass state₀)
    exact wellFormed_preserved hk hd hL δ cfg state₀ hwf

-- Main correctness theorem
theorem tm_correctness {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state₀ : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state₀) :
    decodeTape (forwardPass^[depth] state₀) =
    (tmRun δ cfg depth hL).tape :=
  forwardPass_iter_simulates_tmRun hk hd hL δ cfg state₀ hwf depth

end AgentCompleteness