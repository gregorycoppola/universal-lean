import UniversalLean.AgentCompleteness.Preliminaries

namespace AgentCompleteness

def natToBits (n : ℕ) (width : ℕ) : Fin width → Bool :=
  fun i => (n >>> i.val) % 2 == 1

def bitsToNat (width : ℕ) (bits : Fin width → Bool) : ℕ :=
  Fin.foldl width (fun acc i => acc + if bits i then 2 ^ i.val else 0) 0

-- The value of bit i in n is (n / 2^i) % 2
lemma natToBits_spec (n i : ℕ) (hi : i < 32) :
    natToBits n 32 ⟨i, hi⟩ = true ↔ (n >>> i) % 2 = 1 := by
  simp [natToBits]

-- Each bit contributes its place value
lemma bitsToNat_single (width : ℕ) (bits : Fin width → Bool) (i : Fin width) :
    (if bits i then 2 ^ i.val else 0) ≤ bitsToNat width bits := by
  simp [bitsToNat]
  sorry

-- Core round trip: this is the key number theory lemma
-- Left as sorry: requires induction on bit positions
-- with careful handling of the binary representation
lemma bitsToNat_natToBits (width : ℕ) (n : ℕ) (h : n < 2 ^ width) :
    bitsToNat width (natToBits n width) = n := by
  sorry

-- Bound: bitsToNat is always < 2^width
lemma bitsToNat_lt (width : ℕ) (bits : Fin width → Bool) :
    bitsToNat width bits < 2 ^ width := by
  sorry

-- natToBits is injective on [0, 2^width)
lemma natToBits_inj (width : ℕ) (m n : ℕ)
    (hm : m < 2 ^ width) (hn : n < 2 ^ width)
    (h : natToBits m width = natToBits n width) : m = n := by
  have hm' := bitsToNat_natToBits width m hm
  have hn' := bitsToNat_natToBits width n hn
  rw [← hm', ← hn', h]

-- Zero encodes to all false
lemma natToBits_zero (width : ℕ) (i : Fin width) :
    natToBits 0 width i = false := by
  simp [natToBits]

-- Bit width is sufficient to represent n
lemma bitWidth_sufficient (n : ℕ) (hn : 0 < n) :
    n < 2 ^ (Nat.log2 n + 1) := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by omega) n
  simpa using this

def bitWidth (n : ℕ) : ℕ := Nat.log2 n + 1

lemma bitWidth_spec (n : ℕ) (hn : 0 < n) :
    n < 2 ^ bitWidth n :=
  bitWidth_sufficient n hn

end AgentCompleteness