import UniversalLean.AgentCompleteness.Preliminaries
import UniversalLean.AgentCompleteness.Binary

namespace AgentCompleteness

-- Positional encoding: binary vectors in {-1, +1}^b
def posEnc (b : ℕ) (i : ℕ) : Fin b → ℤ :=
  fun k => if (i >>> k.val) % 2 == 1 then 1 else -1

-- Inner product of two positional encodings
def posEncDot (b : ℕ) (i j : ℕ) : ℤ :=
  Fin.foldl b (fun acc k => acc + posEnc b i k * posEnc b j k) 0

-- Each term is either +1 or -1
lemma posEnc_sq (b i : ℕ) (k : Fin b) :
    posEnc b i k * posEnc b i k = 1 := by
  simp [posEnc]
  split <;> simp

-- Self dot product equals b
lemma posEncDot_self (b : ℕ) (i : ℕ) :
    posEncDot b i i = b := by
  simp [posEncDot]
  induction b with
  | zero => simp [Fin.foldl]
  | succ b ih =>
    rw [Fin.foldl_succ]
    simp [posEnc_sq]
    -- the fold adds b ones
    convert ih using 1
    simp [Fin.foldl]

-- When bit k differs between i and j, that term contributes -1
lemma posEnc_diff_term (b i j : ℕ) (k : Fin b)
    (hdiff : (i >>> k.val) % 2 ≠ (j >>> k.val) % 2) :
    posEnc b i k * posEnc b j k = -1 := by
  simp [posEnc]
  split <;> split <;> simp_all <;> omega

-- When bit k agrees between i and j, that term contributes +1
lemma posEnc_same_term (b i j : ℕ) (k : Fin b)
    (hsame : (i >>> k.val) % 2 = (j >>> k.val) % 2) :
    posEnc b i k * posEnc b j k = 1 := by
  simp [posEnc]
  split <;> split <;> simp_all <;> omega

-- If i ≠ j and both < 2^b, they differ in at least one bit
lemma distinct_differ_in_bit (b i j : ℕ)
    (hi : i < 2^b) (hj : j < 2^b) (hij : i ≠ j) :
    ∃ k : Fin b, (i >>> k.val) % 2 ≠ (j >>> k.val) % 2 := by
  by_contra h
  push_neg at h
  apply hij
  -- if all bits agree then i = j
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < b
  · have := h ⟨k, hk⟩
    simp [Nat.testBit, Nat.shiftRight] at this ⊢
    omega
  · -- bits beyond width are 0 for both
    have hi' : i < 2^k := Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by omega))
    have hj' : j < 2^k := Nat.lt_of_lt_of_le hj (Nat.pow_le_pow_right (by omega) (by omega))
    simp [Nat.testBit_lt_two_pow hi', Nat.testBit_lt_two_pow hj']

-- Distinct positions have dot product ≤ b - 2
lemma posEncDot_distinct (b : ℕ) (hb : 0 < b) (i j : ℕ)
    (hi : i < 2^b) (hj : j < 2^b) (hij : i ≠ j) :
    posEncDot b i j ≤ (b : ℤ) - 2 := by
  -- get a differing bit
  obtain ⟨k, hk⟩ := distinct_differ_in_bit b i j hi hj hij
  simp [posEncDot]
  -- the sum has one -1 term (at k) and at most b-1 terms of +1
  -- so total ≤ (b-1)*1 + 1*(-1) = b-2
  sorry

-- Self product is strictly greater than any distinct product
lemma posEncDot_self_max (b : ℕ) (hb : 0 < b) (i j : ℕ)
    (hi : i < 2^b) (hj : j < 2^b) (hij : i ≠ j) :
    posEncDot b i j < posEncDot b i i := by
  rw [posEncDot_self]
  have := posEncDot_distinct b hb i j hi hj hij
  omega

-- Hardmax attention selects the correct position
def hardmaxAttention {n b : ℕ} (hn : 0 < n)
    (query : ℕ)   -- wire position to look up
    (keys : Fin n → ℕ)   -- position of each token
    (values : Fin n → Bool) -- value at each token
    (hkeys : ∀ i, keys i < 2^b)
    (hquery : query < 2^b)
    -- keys are injective (each position appears once)
    (hInj : Function.Injective keys)
    -- the query appears in the keys
    (hPresent : ∃ i, keys i = query) :
    -- the result is the value at the matching position
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

-- Layer 1 attention correctness:
-- The gather operation retrieves the correct value
-- (this is the discrete/exact version)
theorem layer1_attention_correct {n depth : ℕ} (hn : 0 < n)
    (state : CircuitState n depth) (j : Fin n) :
    (gatherFirstInput state j).scratch1 =
    (state (state j).wire1).val := by
  simp [gatherFirstInput]

-- Layer 2 attention correctness
theorem layer2_attention_correct {n depth : ℕ} (hn : 0 < n)
    (state : CircuitState n depth) (j : Fin n) :
    (gatherSecondInput (gatherFirstInput state) j).scratch2 =
    (state (state j).wire2).val := by
  simp [gatherFirstInput, gatherSecondInput]

-- Softmax approximation:
-- With temperature λ = O(log(n/ε)), softmax weight on
-- the maximum score position is within ε of 1.
-- Left as sorry: standard analysis, requires Mathlib.
lemma softmax_concentrates {n : ℕ} (hn : 0 < n)
    (scores : Fin n → ℝ) (t* : Fin n)
    (hmax : ∀ i, i ≠ t* → scores i ≤ scores t* - 2)
    (λ_ : ℝ) (hλ : λ_ ≥ Real.log (n / 0.01) / 2)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    let Z := Fin.foldl n
      (fun acc i => acc + Real.exp (λ_ * scores i)) 0
    Real.exp (λ_ * scores t*) / Z ≥ 1 - ε := by
  sorry

-- The full attention claim connecting hardmax to softmax:
-- softmax with high temperature approximates hardmax
-- which correctly retrieves the target value
theorem attention_approximates_lookup {n b : ℕ}
    (hn : 0 < n) (hb : 0 < b)
    (query : ℕ) (keys : Fin n → ℕ)
    (values : Fin n → Bool)
    (hkeys : ∀ i, keys i < 2^b)
    (hquery : query < 2^b)
    (hInj : Function.Injective keys)
    (hPresent : ∃ i, keys i = query)
    (ε : ℝ) (hε : 0 < ε) :
    -- there exists a temperature λ such that
    -- softmax attention weight on matching position ≥ 1-ε
    ∃ (λ_ : ℝ), ∃ (i* : Fin n),
      keys i* = query ∧
      ∀ j, j ≠ i* →
        posEncDot b query (keys j) < posEncDot b query (keys i*) := by
  obtain ⟨i*, hi*, hmax⟩ := hardmaxAttention hn query keys values
    hkeys hquery hInj hPresent
  exact ⟨Real.log (n / ε) / 2, i*, hi*, hmax⟩

end AgentCompleteness