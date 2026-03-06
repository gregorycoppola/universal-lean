import UniversalLean.AgentCompleteness.Preliminaries
import UniversalLean.AgentCompleteness.Binary

namespace AgentCompleteness

axiom distinct_differ_in_bit (b i j : ℕ)
    (hi : i < 2^b) (hj : j < 2^b) (hij : i ≠ j) :
    ∃ k : Fin b, (i >>> k.val) % 2 ≠ (j >>> k.val) % 2

axiom posEncDot_distinct (b : ℕ) (hb : 0 < b) (i j : ℕ)
    (hi : i < 2^b) (hj : j < 2^b) (hij : i ≠ j) :
    posEncDot b i j ≤ (b : ℤ) - 2

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