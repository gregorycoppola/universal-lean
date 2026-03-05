import UniversalLean.AgentCompleteness.BooleanGates

namespace AgentCompleteness

-- This file formalizes equation (18) from the paper:
-- the FFN computes all G gate functions in parallel and
-- uses the one-hot gate type vector as a selector.
--
-- yj = Σ_t ReLU([gatej]_t + ft(vi1, vi2) - 1.5) * 2
-- This is nonzero only for the active gate type t*

-- One-hot vector: exactly one position is true
def isOneHot {G : ℕ} (v : Fin G → Bool) : Prop :=
  ∃! t, v t = true

-- The gated selection function over G gate types
-- Given a one-hot selector and two input bits,
-- apply the selected gate function
def gatedSelect (G : ℕ) (selector : Fin G → Bool)
    (gates : Fin G → Bool → Bool → Bool)
    (a b : Bool) : Bool :=
  Fin.foldl G (fun acc t =>
    if selector t then gates t a b else acc) false

-- Gated selection with one-hot selector picks exactly the active gate
lemma gatedSelect_oneHot {G : ℕ} (hG : 0 < G)
    (selector : Fin G → Bool)
    (gates : Fin G → Bool → Bool → Bool)
    (a b : Bool)
    (hOneHot : isOneHot selector)
    (t* : Fin G) (ht : selector t* = true) :
    gatedSelect G selector gates a b = gates t* a b := by
  simp [gatedSelect, isOneHot] at *
  obtain ⟨t, ht_true, ht_unique⟩ := hOneHot
  have heq : t = t* := ht_unique t* ht
  subst heq
  induction G with
  | zero => exact absurd hG (by omega)
  | succ G ih =>
    sorry

-- ReLU gated selection: the real-valued version from equation (18)
-- For one-hot selector s and inputs a, b ∈ {0,1}:
-- Σ_t ReLU(s_t + ft(a,b) - 1.5) * 2 = f_{t*}(a, b)
-- where t* is the unique true position in s
noncomputable def reluGatedSelect (G : ℕ)
    (selector : Fin G → ℝ)   -- one-hot, values in {0,1}
    (gates : Fin G → ℝ → ℝ → ℝ)
    (a b : ℝ) : ℝ :=
  Fin.foldl G (fun acc t =>
    acc + relu (selector t + gates t a b - 1.5) * 2) 0

-- When selector is one-hot with active index t*,
-- reluGatedSelect equals gates t* a b
lemma reluGatedSelect_oneHot (G : ℕ) (hG : 0 < G)
    (selector : Fin G → ℝ)
    (gates : Fin G → ℝ → ℝ → ℝ)
    (a b : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    -- selector is one-hot: one entry is 1, rest are 0
    (t* : Fin G)
    (hActive : selector t* = 1)
    (hInactive : ∀ t, t ≠ t* → selector t = 0)
    -- each gate output is in {0,1}
    (hGates : ∀ t a b, gates t a b ∈ ({0, 1} : Set ℝ)) :
    reluGatedSelect G selector gates a b = gates t* a b := by
  simp [reluGatedSelect]
  sorry

-- The specific gate functions from BooleanGates.lean
-- packaged as a Fin 7 → ℝ → ℝ → ℝ function
noncomputable def standardGates : Fin 7 → ℝ → ℝ → ℝ
  | ⟨0, _⟩ => boolAnd
  | ⟨1, _⟩ => boolOr
  | ⟨2, _⟩ => fun a _ => boolNot a
  | ⟨3, _⟩ => boolNand
  | ⟨4, _⟩ => fun a _ => boolNot a  -- NOR placeholder
  | ⟨5, _⟩ => boolXor
  | ⟨6, _⟩ => boolCopy
  | ⟨n+7, h⟩ => absurd h (by omega)

-- GateType to Fin 7 index
def gateTypeToFin : GateType → Fin 7
  | GateType.AND  => ⟨0, by omega⟩
  | GateType.OR   => ⟨1, by omega⟩
  | GateType.NOT  => ⟨2, by omega⟩
  | GateType.NAND => ⟨3, by omega⟩
  | GateType.NOR  => ⟨4, by omega⟩
  | GateType.XOR  => ⟨5, by omega⟩
  | GateType.COPY => ⟨6, by omega⟩

-- One-hot selector for a gate type
def gateSelector (g : GateType) : Fin 7 → ℝ :=
  fun i => if i = gateTypeToFin g then 1 else 0

-- gateSelector is indeed one-hot
lemma gateSelector_oneHot (g : GateType) :
    (gateSelector g (gateTypeToFin g) = 1) ∧
    (∀ i, i ≠ gateTypeToFin g → gateSelector g i = 0) := by
  constructor
  · simp [gateSelector]
  · intro i hi
    simp [gateSelector, hi]

-- Main FFN theorem: reluGatedSelect with standardGates
-- computes the correct gate function
theorem ffn_gate_selection_correct (g : GateType) (a b : ℝ)
    (ha : a ∈ ({0, 1} : Set ℝ)) (hb : b ∈ ({0, 1} : Set ℝ)) :
    reluGatedSelect 7 (gateSelector g) standardGates a b =
    standardGates (gateTypeToFin g) a b := by
  obtain ⟨hActive, hInactive⟩ := gateSelector_oneHot g
  apply reluGatedSelect_oneHot (by omega) _ _ _ _
    (Set.mem_Icc.mpr ⟨by simp [Set.mem_insert_iff] at ha; cases ha with
      | inl h => linarith [h.symm]
      | inr h => simp at h; linarith, by simp [Set.mem_insert_iff] at ha;
        cases ha with | inl h => linarith [h.symm] | inr h => simp at h; linarith⟩)
    (Set.mem_Icc.mpr ⟨by simp [Set.mem_insert_iff] at hb; cases hb with
      | inl h => linarith [h.symm]
      | inr h => simp at h; linarith, by simp [Set.mem_insert_iff] at hb;
        cases hb with | inl h => linarith [h.symm] | inr h => simp at h; linarith⟩)
    _ hActive hInactive
  intro t a' b'
  fin_cases t <;> simp [standardGates, boolAnd, boolOr, boolNot,
    boolNand, boolXor, boolCopy, relu] <;> sorry

end AgentCompleteness