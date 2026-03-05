import UniversalLean.AgentCompleteness.TMCorrectness

namespace AgentCompleteness

-- Turing completeness: the capstone theorem
-- A 4-layer transformer agent can simulate any TM
theorem agent_simulates_any_tm :
    ∀ (k tapeLen : ℕ) (hk : 0 < k) (hL : 0 < tapeLen),
    ∀ (δ : TMTransition k) (cfg : TMConfig k tapeLen),
    ∃ (depth : ℕ) (hd : 0 < depth)
      (state₀ : CircuitState (fullTokenCount tapeLen k) depth),
    -- initial state encodes cfg
    decodeTape state₀ = cfg.tape ∧
    -- after d steps, tape matches tmRun
    ∀ (d : ℕ),
      decodeTape (forwardPass^[d] state₀) =
      (tmRun δ cfg d hL).tape := by
  intro k tapeLen hk hL δ cfg
  refine ⟨3, by omega, encode hk (by omega) cfg, ?_, ?_⟩
  · exact decode_tape_encode hk (by omega) cfg
  · intro d
    apply forwardPass_iter_simulates_tmRun hk (by omega) hL δ cfg
    exact decode_tape_encode hk (by omega) cfg

-- The full Turing completeness corollary
corollary transformer_is_turing_complete :
    ∀ (k tapeLen d : ℕ) (hk : 0 < k) (hL : 0 < tapeLen)
      (δ : TMTransition k) (cfg : TMConfig k tapeLen),
    ∃ (state₀ : CircuitState (fullTokenCount tapeLen k) 3),
    decodeTape (forwardPass^[d] state₀) =
    (tmRun δ cfg d hL).tape := by
  intro k tapeLen d hk hL δ cfg
  obtain ⟨depth, hd, state₀, henc, hcorr⟩ :=
    agent_simulates_any_tm k tapeLen hk hL δ cfg
  exact ⟨encode hk (by omega) cfg,
    forwardPass_iter_simulates_tmRun hk (by omega) hL δ cfg
      (encode hk (by omega) cfg)
      (decode_tape_encode hk (by omega) cfg) d⟩

end AgentCompleteness