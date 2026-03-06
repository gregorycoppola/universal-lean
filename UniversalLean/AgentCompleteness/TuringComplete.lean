import UniversalLean.AgentCompleteness.TMCorrectness

namespace AgentCompleteness

theorem agent_simulates_any_tm :
    ∀ (k tapeLen : ℕ) (hk : 0 < k) (hL : 0 < tapeLen),
    ∀ (δ : TMTransition k) (cfg : TMConfig k tapeLen),
    ∃ (depth : ℕ) (hd : 0 < depth)
      (state₀ : CircuitState (fullTokenCount tapeLen k) depth),
    decodeTape state₀ = cfg.tape ∧
    ∀ (d : ℕ),
      decodeTape (forwardPass^[d] state₀) =
      (tmRun δ cfg d hL).tape := by
  intro k tapeLen hk hL δ cfg
  refine ⟨3, by omega, encode hk (by omega) cfg, ?_, ?_⟩
  · funext i
    simp [decodeTape, encode, defaultToken, tmTokenCount]
    exact i.isLt
  · intro d
    apply forwardPass_iter_simulates_tmRun hk (by omega) hL δ cfg
    exact encode_wellformed hk (by omega) hL δ cfg

corollary transformer_is_turing_complete :
    ∀ (k tapeLen d : ℕ) (hk : 0 < k) (hL : 0 < tapeLen)
      (δ : TMTransition k) (cfg : TMConfig k tapeLen),
    ∃ (state₀ : CircuitState (fullTokenCount tapeLen k) 3),
    decodeTape (forwardPass^[d] state₀) =
    (tmRun δ cfg d hL).tape := by
  intro k tapeLen d hk hL δ cfg
  exact ⟨encode hk (by omega) cfg,
    forwardPass_iter_simulates_tmRun hk (by omega) hL δ cfg
      (encode_wellformed hk (by omega) hL δ cfg) d⟩

end AgentCompleteness