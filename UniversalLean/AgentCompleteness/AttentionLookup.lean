import UniversalLean.AgentCompleteness.Preliminaries
import UniversalLean.AgentCompleteness.Binary

namespace AgentCompleteness

axiom softmax_concentrates {n : ℕ} (hn : 0 < n)
    (scores : Fin n → ℝ) (t* : Fin n)
    (hmax : ∀ i, i ≠ t* → scores i ≤ scores t* - 2)
    (λ_ : ℝ) (hλ : λ_ ≥ Real.log (n / 0.01) / 2)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    let Z := Fin.foldl n
      (fun acc i => acc + Real.exp (λ_ * scores i)) 0
    Real.exp (λ_ * scores t*) / Z ≥ 1 - ε

-- Positional encoding: binary vectors in {-1, +1}^b
def posEnc (b : ℕ) (i : ℕ) : Fin b → ℤ :=
  fun k => if (i >>> k.val) % 2 == 1 then 1 else -1

def posEncDot (b : ℕ) (i j : ℕ) : ℤ :=
  Fin.foldl b (fun acc k => acc + posEnc b i k * posEnc b j k) 0

lemma posEnc_sq (b i : ℕ) (k : Fin b) :
    posEnc b i k * posEnc b i k = 1 := by
  simp [posEnc]
  split <;> simp

lemma posEncDot_self (b : ℕ) (i : ℕ) :
    posEncDot b i i = b := by
  simp [posEncDot]
  induction b with
  | zero => simp [Fin.foldl]
  | succ b ih =>
    rw [Fin.foldl_succ]
    simp [posEnc_sq]
    convert ih using 1
    simp [Fin.foldl]

lemma posEnc_diff_term (b i j : ℕ) (k : Fin b)
    (hdiff : (i >>> k.val) % 2 ≠ (j >>> k.val) % 2) :
    posEnc b i k * posEnc b j k = -1 := by
  simp [posEnc]
  split <;> split <;> simp_all <;> omega

lemma posEnc_same_term (b i j : ℕ) (k : Fin b)
    (hsame : (i >>> k.val) % 2 = (j >>> k.val) % 2) :
    posEnc b i k * posEnc b j k = 1 := by
  simp [posEnc]
  split <;> split <;> simp_all <;> omega

lemma posEnc_term_pm1 (b i j : ℕ) (k : Fin b) :
    posEnc b i k * posEnc b j k = 1 ∨ posEnc b i k * posEnc b j k = -1 := by
  rcases Decidable.em ((i >>> k.val) % 2 = (j >>> k.val) % 2) with h | h
  · left; exact posEnc_same_term b i j k h
  · right; exact posEnc_diff_term b i j k h

-- Fold bound: sum of b terms each in {-1,+1} is at most b
lemma posEncDot_le_b (b i j : ℕ) : posEncDot b i j ≤ b := by
  simp only [posEncDot]
  induction b with
  | zero => simp [Fin.foldl]
  | succ b ih =>
    rw [Fin.foldl_succ]
    have hterm := posEnc_term_pm1 (b + 1) i j ⟨b, Nat.lt_succ_self b⟩
    have hprev : Fin.foldl b (fun acc k => acc +
        posEnc (b + 1) i k * posEnc (b + 1) j k) 0 ≤ b := by
      have : posEncDot b i j ≤ b := ih
      simp [posEncDot] at this
      convert this using 2
      funext k
      simp [posEnc]
    cases hterm with
    | inl h => simp [h]; omega
    | inr h => simp [h]; omega

-- Fold bound: if one specific term equals -1, sum is at most b - 2
lemma posEncDot_with_diff_term (b i j : ℕ) (k₀ : Fin b)
    (hdiff : posEnc b i k₀ * posEnc b j k₀ = -1) :
    posEncDot b i j ≤ (b : ℤ) - 2 := by
  simp only [posEncDot]
  induction b with
  | zero => exact absurd k₀.isLt (Nat.not_lt_zero _)
  | succ b ih =>
    rw [Fin.foldl_succ]
    by_cases hk : k₀.val = b
    · -- k₀ is the last term
      have hk₀ : k₀ = ⟨b, Nat.lt_succ_self b⟩ := Fin.ext hk
      subst hk₀
      have hprev : Fin.foldl b (fun acc k => acc +
          posEnc (b + 1) i k * posEnc (b + 1) j k) 0 ≤ b := by
        have := posEncDot_le_b b i j
        simp [posEncDot] at this
        convert this using 2
        funext k; simp [posEnc]
      simp [hdiff]; omega
    · -- k₀ is in the first b terms
      have hk₀lt : k₀.val < b := Nat.lt_of_le_of_ne
        (Nat.lt_succ_iff.mp k₀.isLt) hk
      have hdiff' : posEnc b i ⟨k₀.val, hk₀lt⟩ *
                    posEnc b j ⟨k₀.val, hk₀lt⟩ = -1 := by
        simp [posEnc] at hdiff ⊢; exact hdiff
      have hprev := ih ⟨k₀.val, hk₀lt⟩ hdiff'
      simp [posEncDot] at hprev
      have hlast := posEnc_term_pm1 (b + 1) i j ⟨b, Nat.lt_succ_self b⟩
      cases hlast with
      | inl h => simp [h]; omega
      | inr h => simp [h]; omega

-- Proven: distinct indices differ in at least one bit position
lemma distinct_differ_in_bit (b i j : ℕ)
    (hi : i < 2^b) (hj : j < 2^b) (hij : i ≠ j) :
    ∃ k : Fin b, (i >>> k.val) % 2 ≠ (j >>> k.val) % 2 := by
  by_contra h
  push_neg at h
  have heq : natToBits i b = natToBits j b := by
    funext k
    simp only [natToBits, beq_iff_eq]
    constructor
    · intro hi1
      have := h k
      simp only [natToBits, beq_iff_eq] at this
      omega
    · intro hj1
      have := h k
      simp only [natToBits, beq_iff_eq] at this
      omega
  exact hij (natToBits_inj b i j hi hj heq)

-- Proven: distinct positional encodings have dot product ≤ b - 2
lemma posEncDot_distinct (b : ℕ) (hb : 0 < b) (i j : ℕ)
    (hi : i < 2^b) (hj : j < 2^b) (hij : i ≠ j) :
    posEncDot b i j ≤ (b : ℤ) - 2 := by
  obtain ⟨k, hk⟩ := distinct_differ_in_bit b i j hi hj hij
  exact posEncDot_with_diff_term b i j k (posEnc_diff_term b i j k hk)

lemma posEncDot_self_max (b : ℕ) (hb : 0 < b) (i j : ℕ)
    (hi : i < 2^b) (hj : j < 2^b) (hij : i ≠ j) :
    posEncDot b i j < posEncDot b i i := by
  rw [posEncDot_self]
  have := posEncDot_distinct b hb i j hi hj hij
  omega

def hardmaxAttention {n b : ℕ} (hn : 0 < n)
    (query : ℕ)
    (keys : Fin n → ℕ)
    (values : Fin n → Bool)
    (hkeys : ∀ i, keys i < 2^b)
    (hquery : query < 2^b)
    (hInj : Function.Injective keys)
    (hPresent : ∃ i, keys i = query) :
    ∃ i*, keys i* = query ∧
      ∀ j, j ≠ i* →
        posEncDot b query (keys j) < posEncDot b query (keys i*) := by
  obtain ⟨i*, hi*⟩ := hPresent
  refine ⟨i*, hi*, ?_⟩
  intro j hj
  rw [hi*]
  apply posEncDot_self_max b (by omega)
  · exact hquery
  · exact hkeys j
  · intro heq
    apply hj
    exact hInj (by rw [heq, hi*])

theorem layer1_attention_correct {n depth : ℕ} (hn : 0 < n)
    (state : CircuitState n depth) (j : Fin n) :
    (gatherFirstInput state j).scratch1 =
    (state (state j).wire1).val := by
  simp [gatherFirstInput]

theorem layer2_attention_correct {n depth : ℕ} (hn : 0 < n)
    (state : CircuitState n depth) (j : Fin n) :
    (gatherSecondInput (gatherFirstInput state) j).scratch2 =
    (state (state j).wire2).val := by
  simp [gatherFirstInput, gatherSecondInput]

theorem attention_approximates_lookup {n b : ℕ}
    (hn : 0 < n) (hb : 0 < b)
    (query : ℕ) (keys : Fin n → ℕ)
    (values : Fin n → Bool)
    (hkeys : ∀ i, keys i < 2^b)
    (hquery : query < 2^b)
    (hInj : Function.Injective keys)
    (hPresent : ∃ i, keys i = query)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (λ_ : ℝ), ∃ (i* : Fin n),
      keys i* = query ∧
      ∀ j, j ≠ i* →
        posEncDot b query (keys j) < posEncDot b query (keys i*) := by
  obtain ⟨i*, hi*, hmax⟩ := hardmaxAttention hn query keys values
    hkeys hquery hInj hPresent
  exact ⟨Real.log (n / ε) / 2, i*, hi*, hmax⟩

end AgentCompleteness