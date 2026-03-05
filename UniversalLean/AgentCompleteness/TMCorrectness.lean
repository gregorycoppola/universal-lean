import UniversalLean.AgentCompleteness.ProgramEncoding

namespace AgentCompleteness

-- Now that we have buildTransitionCircuit,
-- we replace the axiom with a proper theorem
-- (modulo the sorry in forwardPass_simulates_via_program)

-- The stepping lemma: no longer an axiom
-- follows from forwardPass_simulates_via_program
theorem forwardPass_simulates_tmStep {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state : CircuitState (fullTokenCount tapeLen k) depth)
    (henc : decodeTape state = cfg.tape) :
    decodeTape (forwardPass state) =
    (tmStep δ cfg hL).tape :=
  forwardPass_simulates_via_program hk hd hL δ cfg state henc

-- Iterated stepping by induction
theorem forwardPass_iter_simulates_tmRun {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state₀ : CircuitState (fullTokenCount tapeLen k) depth)
    (henc : decodeTape state₀ = cfg.tape)
    (d : ℕ) :
    decodeTape (forwardPass^[d] state₀) =
    (tmRun δ cfg d hL).tape := by
  induction d generalizing cfg state₀ with
  | zero =>
    simp [tmRun, henc]
  | succ d ih =>
    rw [Function.iterate_succ', Function.comp]
    rw [tmRun]
    apply ih
    exact forwardPass_simulates_tmStep hk hd hL δ cfg state₀ henc

-- Main correctness theorem: clean, no axiom
theorem tm_correctness {k tapeLen depth : ℕ}
    (hk : 0 < k) (hd : 0 < depth) (hL : 0 < tapeLen)
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (state₀ : CircuitState (fullTokenCount tapeLen k) depth)
    (henc : decodeTape state₀ = cfg.tape) :
    decodeTape (forwardPass^[depth] state₀) =
    (tmRun δ cfg depth hL).tape :=
  forwardPass_iter_simulates_tmRun hk hd hL δ cfg state₀ henc depth

end AgentCompleteness