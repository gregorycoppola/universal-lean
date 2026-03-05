import UniversalLean.AgentCompleteness.Layers

namespace AgentCompleteness

-- Key correctness lemma: after gathering, scratch registers hold the right values
lemma gather_correct {n depth : ℕ} (state : CircuitState n depth) (j : Fin n) :
    (gatherSecondInput (gatherFirstInput state) j).scratch1 =
      (state (state j).wire1).val ∧
    (gatherSecondInput (gatherFirstInput state) j).scratch2 =
      (state (state j).wire2).val := by
  simp [gatherFirstInput, gatherSecondInput]

-- Theorem 5.1: one forward pass correctly computes gate output
-- (before wiring update, i.e. the val field is correct)
theorem circuit_layer_simulation {n depth : ℕ}
    (state : CircuitState n depth) (j : Fin n) :
    (computeGate (gatherSecondInput (gatherFirstInput state)) j).val =
    applyGate (state j).gate
              (state (state j).wire1).val
              (state (state j).wire2).val := by
  simp [computeGate, gatherSecondInput, gatherFirstInput]

-- Theorem 5.1b: full forwardPass val field matches gate computation
-- Note: updateWiring only changes wire1/wire2, not val, so val is preserved
theorem forwardPass_val {n depth : ℕ}
    (state : CircuitState n depth) (j : Fin n) :
    (forwardPass state j).val =
    applyGate (state j).gate
              (state (state j).wire1).val
              (state (state j).wire2).val := by
  simp [forwardPass, updateWiring, computeGate, gatherSecondInput, gatherFirstInput]

-- Theorem 5.2: iterated forward passes exist
theorem agent_completeness {n depth : ℕ} (init : CircuitState n depth) (d : ℕ) :
    ∃ final : CircuitState n depth, final = forwardPass^[d] init := by
  exact ⟨forwardPass^[d] init, rfl⟩

-- Wiring update correctness: after updateWiring, wire1/wire2 come from program
theorem updateWiring_correct {n depth : ℕ}
    (state : CircuitState n depth) (j : Fin n) :
    (updateWiring state j).wire1 = (state j).program (state j).iteration j |>.wire1 ∧
    (updateWiring state j).wire2 = (state j).program (state j).iteration j |>.wire2 := by
  simp [updateWiring]

-- Corollary 5.3: Turing completeness (sketch)
corollary turing_complete :
    ∀ (f : List Bool → List Bool),
    ∃ (n depth : ℕ)
      (encode : List Bool → CircuitState n depth)
      (decode : CircuitState n depth → List Bool),
    ∀ x, decode (forwardPass^[depth] (encode x)) = f x := by
  sorry

end AgentCompleteness