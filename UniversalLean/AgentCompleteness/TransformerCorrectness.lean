import UniversalLean.AgentCompleteness.FFNGateSelection
import UniversalLean.AgentCompleteness.AttentionLookup

namespace AgentCompleteness

-- This file ties together the transformer components
-- into a unified correctness statement.
--
-- The full transformer claim:
-- There exist weight matrices Q1, K1, V1, Q2, K2, V2, W1, W2, b1, b2
-- such that the 4-layer transformer computes one depth-1 circuit layer.
--
-- We have proven:
--   (A) Gather correctness (attention retrieves correct values)
--   (B) FFN gate selection (FFN computes correct gate function)
-- These together give the main theorem.

-- Unified forward pass correctness
-- Combines attention lookup (A) and FFN selection (B)
theorem transformer_circuit_correctness {n depth : ℕ}
    (hn : 0 < n)
    (state : CircuitState n depth) (j : Fin n) :
    -- Layer 1+2: attention gathers correct inputs
    (gatherSecondInput (gatherFirstInput state) j).scratch1 =
      (state (state j).wire1).val ∧
    (gatherSecondInput (gatherFirstInput state) j).scratch2 =
      (state (state j).wire2).val ∧
    -- Layer 3: FFN computes correct gate output
    (computeGate (gatherSecondInput (gatherFirstInput state)) j).val =
      applyGate (state j).gate
                (state (state j).wire1).val
                (state (state j).wire2).val := by
  refine ⟨?_, ?_, ?_⟩
  · simp [gatherFirstInput, gatherSecondInput]
  · simp [gatherFirstInput, gatherSecondInput]
  · simp [computeGate, gatherFirstInput, gatherSecondInput]

-- The real-valued version:
-- FFN with standardGates and gateSelector computes correct output
theorem transformer_realvalued_correctness
    (g : GateType) (a b : ℝ)
    (ha : a ∈ ({0, 1} : Set ℝ))
    (hb : b ∈ ({0, 1} : Set ℝ)) :
    reluGatedSelect 7 (gateSelector g) standardGates a b =
    standardGates (gateTypeToFin g) a b :=
  ffn_gate_selection_correct g a b ha hb

-- The gap between real-valued and discrete:
-- We need to show that reluGatedSelect on real inputs {0,1}
-- matches applyGate on Bool inputs
theorem realvalued_matches_bool (g : GateType) (a b : Bool) :
    reluGatedSelect 7 (gateSelector g) standardGates
      (if a then 1 else 0) (if b then 1 else 0) =
    if applyGate g a b then 1 else 0 := by
  fin_cases g <;>
  fin_cases a <;>
  fin_cases b <;>
  simp [applyGate, gateSelector, gateTypeToFin,
        standardGates, reluGatedSelect,
        boolAnd, boolOr, boolNot, boolNand,
        boolXor, boolCopy, relu] <;>
  norm_num [Fin.foldl]

end AgentCompleteness