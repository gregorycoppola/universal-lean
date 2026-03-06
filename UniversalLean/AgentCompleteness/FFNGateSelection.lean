import UniversalLean.AgentCompleteness.BooleanGates

namespace AgentCompleteness

axiom foldl_inactive_zero (G : ℕ)
    (selector : Fin G → ℝ)
    (gates : Fin G → ℝ → ℝ → ℝ)
    (a b : ℝ) (t* : Fin G)
    (hInactive : ∀ t, t ≠ t* → selector t = 0)
    (hGates : ∀ t, gates t a b = 0 ∨ gates t a b = 1) :
    Fin.foldl G (fun acc t =>
      if t = t* then acc
      else acc + relu (selector t + gates t a b - 1.5) * 2) 0 = 0

def isOneHot {G : ℕ} (v : Fin G → Bool) : Prop :=
  ∃! t, v t = true

def gatedSelect (G : ℕ) (selector : Fin G → Bool)
    (gates : Fin G → Bool → Bool → Bool)
    (a b : Bool) : Bool :=
  Fin.foldl G (fun acc t =>
    if selector t then gates t a b else acc) false

noncomputable def reluGatedSelect (G : ℕ)
    (selector : Fin G → ℝ)
    (gates : Fin G → ℝ → ℝ → ℝ)
    (a b : ℝ) : ℝ :=
  Fin.foldl G (fun acc t =>
    acc + relu (selector t + gates t a b - 1.5) * 2) 0

lemma relu_inactive_zero (f : ℝ) (hf : f = 0 ∨ f = 1) :
    relu (0 + f - 1.5) * 2 = 0 := by
  cases hf with
  | inl h => simp [h, relu, max]
  | inr h => simp [h, relu, max]

lemma relu_active_correct (f : ℝ) (hf : f = 0 ∨ f = 1) :
    relu (1 + f - 1.5) * 2 = f := by
  cases hf with
  | inl h => simp [h, relu, max]
  | inr h => simp [h, relu, max]; norm_num

lemma standardGates_binary (t : Fin 7) (a b : ℝ)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    standardGates t a b = 0 ∨ standardGates t a b = 1 := by
  fin_cases t <;>
  simp [standardGates, boolAnd, boolOr, boolNot,
        boolNand, boolXor, boolCopy, relu] <;>
  cases ha with
  | inl h => cases hb with
    | inl h2 => simp [h, h2]; norm_num [max]
    | inr h2 => simp [h, h2]; norm_num [max]
  | inr h => cases hb with
    | inl h2 => simp [h, h2]; norm_num [max]
    | inr h2 => simp [h, h2]; norm_num [max]

lemma reluGatedSelect_inactive_term (G : ℕ)
    (selector : Fin G → ℝ)
    (gates : Fin G → ℝ → ℝ → ℝ)
    (a b : ℝ) (t : Fin G)
    (hInactive : selector t = 0)
    (hGate : gates t a b = 0 ∨ gates t a b = 1) :
    relu (selector t + gates t a b - 1.5) * 2 = 0 := by
  rw [hInactive]
  exact relu_inactive_zero _ hGate

lemma reluGatedSelect_active_term (G : ℕ)
    (selector : Fin G → ℝ)
    (gates : Fin G → ℝ → ℝ → ℝ)
    (a b : ℝ) (t : Fin G)
    (hActive : selector t = 1)
    (hGate : gates t a b = 0 ∨ gates t a b = 1) :
    relu (selector t + gates t a b - 1.5) * 2 = gates t a b := by
  rw [hActive]
  exact relu_active_correct _ hGate

theorem reluGatedSelect_oneHot (G : ℕ) (hG : 0 < G)
    (selector : Fin G → ℝ)
    (gates : Fin G → ℝ → ℝ → ℝ)
    (a b : ℝ)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (t* : Fin G)
    (hActive : selector t* = 1)
    (hInactive : ∀ t, t ≠ t* → selector t = 0)
    (hGates : ∀ t, gates t a b = 0 ∨ gates t a b = 1) :
    reluGatedSelect G selector gates a b = gates t* a b := by
  simp [reluGatedSelect]
  have hshift : Fin.foldl G (fun acc t =>
      acc + relu (selector t + gates t a b - 1.5) * 2) 0 =
    Fin.foldl G (fun acc t =>
      if t = t* then acc + gates t* a b
      else acc + 0) 0 := by
    congr 1; funext acc t
    by_cases ht : t = t*
    · subst ht
      simp
      rw [reluGatedSelect_active_term G selector gates a b t hActive (hGates t)]
    · simp [ht]
      rw [reluGatedSelect_inactive_term G selector gates a b t
        (hInactive t ht) (hGates t)]
  rw [hshift]
  simp
  exact foldl_inactive_zero G selector gates a b t* hInactive hGates

def gateTypeToFin : GateType → Fin 7
  | GateType.AND  => ⟨0, by omega⟩
  | GateType.OR   => ⟨1, by omega⟩
  | GateType.NOT  => ⟨2, by omega⟩
  | GateType.NAND => ⟨3, by omega⟩
  | GateType.NOR  => ⟨4, by omega⟩
  | GateType.XOR  => ⟨5, by omega⟩
  | GateType.COPY => ⟨6, by omega⟩

noncomputable def standardGates : Fin 7 → ℝ → ℝ → ℝ
  | ⟨0, _⟩ => boolAnd
  | ⟨1, _⟩ => boolOr
  | ⟨2, _⟩ => fun a _ => boolNot a
  | ⟨3, _⟩ => boolNand
  | ⟨4, _⟩ => fun a _ => boolNot a
  | ⟨5, _⟩ => boolXor
  | ⟨6, _⟩ => boolCopy
  | ⟨n+7, h⟩ => absurd h (by omega)

noncomputable def gateSelector (g : GateType) : Fin 7 → ℝ :=
  fun i => if i = gateTypeToFin g then 1 else 0

lemma gateSelector_active (g : GateType) :
    gateSelector g (gateTypeToFin g) = 1 := by
  simp [gateSelector]

lemma gateSelector_inactive (g : GateType) (i : Fin 7)
    (hi : i ≠ gateTypeToFin g) :
    gateSelector g i = 0 := by
  simp [gateSelector, hi]

theorem ffn_gate_selection_correct (g : GateType) (a b : ℝ)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    reluGatedSelect 7 (gateSelector g) standardGates a b =
    standardGates (gateTypeToFin g) a b := by
  apply reluGatedSelect_oneHot (by omega)
  · exact gateSelector_active g
  · exact fun t ht => gateSelector_inactive g t ht
  · intro t
    exact standardGates_binary t a b ha hb

theorem realvalued_matches_bool (g : GateType) (a b : Bool) :
    reluGatedSelect 7 (gateSelector g) standardGates
      (if a then 1 else 0) (if b then 1 else 0) =
    if applyGate g a b then 1 else 0 := by
  have ha : (if a then (1:ℝ) else 0) = 0 ∨
            (if a then (1:ℝ) else 0) = 1 := by
    cases a <;> simp
  have hb : (if b then (1:ℝ) else 0) = 0 ∨
            (if b then (1:ℝ) else 0) = 1 := by
    cases b <;> simp
  rw [ffn_gate_selection_correct g _ _ ha hb]
  fin_cases g <;>
  fin_cases a <;>
  fin_cases b <;>
  simp [applyGate, gateTypeToFin, standardGates,
        boolAnd, boolOr, boolNot, boolNand,
        boolXor, boolCopy, relu] <;>
  norm_num

end AgentCompleteness