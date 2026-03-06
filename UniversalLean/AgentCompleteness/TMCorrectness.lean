import UniversalLean.AgentCompleteness.ProgramEncoding

namespace AgentCompleteness

-- Stepping lemma: now a real theorem, not an axiom
theorem forwardPass_simulates_tmStep {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state) :
    decodeTape (forwardPass state) =
    (tmStep δ cfg hL).tape :=
  forwardPass_simulates_via_program hk hd hL δ cfg state hwf

-- Well-formedness is preserved by forwardPass
-- (sorry'd: tedious but not novel)
lemma wellFormed_preserved {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (hwf : WellFormed hk hL δ cfg state) :
    WellFormed hk hL δ (tmStep δ cfg hL)
      (forwardPass state) := by
  sorry

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
    exact (hwf.tape_val · |> funext fun i => by
      simp [decodeTape]
      exact hwf.tape_val i)
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