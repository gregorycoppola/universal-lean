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

lemma flipTM_head_pos {tapeLen : ℕ} (hL : 0 < tapeLen) (d : ℕ)
    (hd : d < tapeLen) :
    (tmRun flipTM (flipInitConfig tapeLen hL) d hL).head = ⟨d, by omega⟩ := by
  induction d with
  | zero => simp [tmRun, flipInitConfig]
  | succ d ih =>
    have hd' : d < tapeLen := by omega
    rw [tmRun, ih hd']
    simp [tmStep, flipTM]
    constructor
    · omega
    · rfl

lemma flipTM_state_after {tapeLen : ℕ} (hL : 0 < tapeLen) (d : ℕ)
    (hd : d ≤ tapeLen) :
    (tmRun flipTM (flipInitConfig tapeLen hL) d hL).state = ⟨0, by omega⟩ := by
  induction d with
  | zero => simp [tmRun, flipInitConfig]
  | succ d ih =>
    have hd' : d ≤ tapeLen := by omega
    have hd'' : d < tapeLen := by omega
    rw [tmRun, ih hd']
    simp [tmStep, flipTM]
    rfl

lemma flipInit_tape_false {tapeLen : ℕ} (hL : 0 < tapeLen) (i : Fin tapeLen) :
    (flipInitConfig tapeLen hL).tape i = false := by
  simp [flipInitConfig]

lemma flipTM_tape_after_head {tapeLen : ℕ} (hL : 0 < tapeLen) (d : ℕ)
    (hd : d ≤ tapeLen) (i : Fin tapeLen) (hi : d ≤ i.val) :
    (tmRun flipTM (flipInitConfig tapeLen hL) d hL).tape i = false := by
  induction d with
  | zero => simp [tmRun, flipInitConfig]
  | succ d ih =>
    have hd' : d ≤ tapeLen := by omega
    have hd'' : d < tapeLen := by omega
    have hi' : d ≤ i.val := by omega
    rw [tmRun]
    simp [tmStep, flipTM]
    rw [flipTM_state_after hL d hd']
    rw [flipTM_head_pos hL d hd'']
    simp
    intro heq
    have hne : i.val ≠ d := by omega
    have : i ≠ ⟨d, hd''⟩ := by
      intro h; apply hne; exact congrArg Fin.val h
    simp [this]
    exact ih hd' hi'

lemma flipTM_tape_before_head {tapeLen : ℕ} (hL : 0 < tapeLen) (d : ℕ)
    (hd : d ≤ tapeLen) (i : Fin tapeLen) (hi : i.val < d) :
    (tmRun flipTM (flipInitConfig tapeLen hL) d hL).tape i = true := by
  induction d with
  | zero => omega
  | succ d ih =>
    have hd' : d ≤ tapeLen := by omega
    have hd'' : d < tapeLen := by omega
    rw [tmRun]
    simp [tmStep, flipTM]
    rw [flipTM_state_after hL d hd']
    rw [flipTM_head_pos hL d hd'']
    simp
    by_cases hid : i.val < d
    · have prev := ih hd' hid
      have hne : i ≠ ⟨d, hd''⟩ := by
        intro h; have : i.val = d := congrArg Fin.val h; omega
      simp [hne, prev]
    · have heq : i.val = d := by omega
      have hifin : i = ⟨d, hd''⟩ := by apply Fin.ext; exact heq
      subst hifin
      simp
      have := flipTM_tape_after_head hL d hd' ⟨d, hd''⟩ (le_refl d)
      simp at this
      simp [this]

lemma flipTM_flips_all {tapeLen : ℕ} (hL : 0 < tapeLen) (i : Fin tapeLen) :
    (tmRun flipTM (flipInitConfig tapeLen hL) tapeLen hL).tape i = true :=
  flipTM_tape_before_head hL tapeLen (le_refl _) i i.isLt

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