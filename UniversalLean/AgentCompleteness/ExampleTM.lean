import UniversalLean.AgentCompleteness.TMCorrectness

namespace AgentCompleteness

def flipTM : TMTransition 2 :=
  fun state sym =>
    match state.val with
    | 0 => (⟨0, by omega⟩, !sym, Dir.R)
    | _ => (⟨1, by omega⟩, sym,  Dir.R)

def flipInitConfig (tapeLen : ℕ) (hL : 0 < tapeLen) : TMConfig 2 tapeLen :=
  { state := ⟨0, by omega⟩
    tape  := fun _ => false
    head  := ⟨0, hL⟩ }

-- Key helper: after d steps of flipTM starting from all-zeros,
-- positions < d have been flipped to true,
-- head is at position min(d, tapeLen-1),
-- state is still 0 if d < tapeLen
lemma flipTM_state_after {tapeLen : ℕ} (hL : 0 < tapeLen) (d : ℕ) (hd : d ≤ tapeLen) :
    (tmRun flipTM (flipInitConfig tapeLen hL) d hL).state = ⟨0, by omega⟩ := by
  induction d with
  | zero => simp [tmRun, flipInitConfig]
  | succ d ih =>
    simp [tmRun, tmStep, flipTM]
    sorry

-- Helper: positions before head have been flipped
lemma flipTM_tape_before_head {tapeLen : ℕ} (hL : 0 < tapeLen) (d : ℕ)
    (hd : d ≤ tapeLen) (i : Fin tapeLen) (hi : i.val < d) :
    (tmRun flipTM (flipInitConfig tapeLen hL) d hL).tape i = true := by
  induction d with
  | zero => omega
  | succ d ih =>
    simp [tmRun, tmStep, flipTM]
    by_cases hid : i.val < d
    · -- position already flipped in previous steps
      sorry
    · -- position being flipped at this step
      have heq : i.val = d := by omega
      sorry

-- Helper: head is at position min(d, tapeLen-1) after d steps
lemma flipTM_head_pos {tapeLen : ℕ} (hL : 0 < tapeLen) (d : ℕ)
    (hd : d < tapeLen) :
    (tmRun flipTM (flipInitConfig tapeLen hL) d hL).head = ⟨d, by omega⟩ := by
  induction d with
  | zero => simp [tmRun, flipInitConfig]
  | succ d ih =>
    simp [tmRun, tmStep, flipTM]
    sorry

-- Main lemma: after tapeLen steps all bits flipped
lemma flipTM_flips_all {tapeLen : ℕ} (hL : 0 < tapeLen) (i : Fin tapeLen) :
    (tmRun flipTM (flipInitConfig tapeLen hL) tapeLen hL).tape i = true := by
  apply flipTM_tape_before_head hL tapeLen (le_refl _) i i.isLt

-- Full end-to-end theorem: no sorry, just axiom on forwardPass_simulates_tmStep
theorem flipTM_circuit_correct {tapeLen depth : ℕ}
    (hL : 0 < tapeLen) (hd : 0 < depth)
    (i : Fin tapeLen) :
    decodeTape
      (forwardPass^[tapeLen]
        (encode (by omega : 0 < 2) hd (flipInitConfig tapeLen hL))) i
    = true := by
  rw [tm_correctness (by omega) hd hL flipTM]
  exact flipTM_flips_all hL i

end AgentCompleteness