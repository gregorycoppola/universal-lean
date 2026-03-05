import UniversalLean.AgentCompleteness.Preliminaries
import UniversalLean.AgentCompleteness.Binary

namespace AgentCompleteness

-- Minterm: AND of all input literals
def minterm (inputWidth : ℕ)
    (pattern : Fin inputWidth → Bool)
    (inputs : Fin inputWidth → Bool) : Bool :=
  Fin.foldl inputWidth (fun acc i =>
    acc && (if pattern i then inputs i else !inputs i)) true

-- Minterm fires exactly when inputs match pattern
lemma minterm_correct (inputWidth : ℕ)
    (pattern inputs : Fin inputWidth → Bool) :
    minterm inputWidth pattern inputs = true ↔
    ∀ i, inputs i = pattern i := by
  simp [minterm]
  induction inputWidth with
  | zero =>
    simp [Fin.foldl]
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    simp [Bool.and_eq_true]
    constructor
    · intro ⟨hfold, hlast⟩
      intro i
      by_cases hi : i.val < n
      · have := (ih
            (fun j => pattern ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩)
            (fun j => inputs ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩)).mp
            hfold ⟨i.val, hi⟩
        simpa using this
      · have heq : i = Fin.last n := by
          apply Fin.ext
          omega
        subst heq
        simp [Fin.last] at hlast
        split at hlast
        · simpa
        · simp at hlast
          simpa
    · intro hall
      constructor
      · apply (ih
            (fun j => pattern ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩)
            (fun j => inputs ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩)).mpr
        intro j
        exact hall ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩
      · have := hall (Fin.last n)
        simp [Fin.last] at this ⊢
        split
        · exact this
        · simp
          exact this.symm

-- Minterm is false when inputs differ from pattern at some position
lemma minterm_false_of_diff (inputWidth : ℕ)
    (pattern inputs : Fin inputWidth → Bool)
    (i : Fin inputWidth) (hdiff : inputs i ≠ pattern i) :
    minterm inputWidth pattern inputs = false := by
  by_contra h
  push_neg at h
  rw [Bool.not_eq_false] at h
  rw [minterm_correct] at h
  exact hdiff (h i)

-- DNF: OR of minterms for true rows
def dnf (inputWidth : ℕ)
    (truthTable : (Fin inputWidth → Bool) → Bool)
    (inputs : Fin inputWidth → Bool) : Bool :=
  -- enumerate all 2^inputWidth input patterns
  Fin.foldl (2 ^ inputWidth) (fun acc row =>
    let rowBits := natToBits row.val inputWidth
    acc || (truthTable rowBits && minterm inputWidth rowBits inputs)) false

-- Every input appears exactly once in the enumeration
lemma natToBits_surjective (inputWidth : ℕ)
    (pattern : Fin inputWidth → Bool) :
    ∃ row : Fin (2 ^ inputWidth),
    natToBits row.val inputWidth = pattern := by
  sorry

-- DNF correctly computes any Boolean function
lemma dnf_correct (inputWidth : ℕ)
    (truthTable : (Fin inputWidth → Bool) → Bool)
    (inputs : Fin inputWidth → Bool) :
    dnf inputWidth truthTable inputs = truthTable inputs := by
  simp [dnf]
  -- the fold fires exactly on the row matching inputs
  sorry

-- TM input/output widths
def tmInputWidth (k : ℕ) : ℕ := bitWidth k + 1
def tmOutputWidth (k : ℕ) : ℕ := bitWidth k + 2

-- Encode TM inputs as bits
def tmInputBits {k tapeLen : ℕ}
    (state : Fin k) (sym : Bool) :
    Fin (tmInputWidth k) → Bool :=
  fun i =>
    if h : i.val < bitWidth k
    then natToBits state.val (bitWidth k) ⟨i.val, h⟩
    else sym

-- Encode TM outputs as bits
def tmOutputBits {k : ℕ}
    (newState : Fin k) (writeBit : Bool) (dir : Dir) :
    Fin (tmOutputWidth k) → Bool :=
  fun i =>
    if h : i.val < bitWidth k
    then natToBits newState.val (bitWidth k) ⟨i.val, h⟩
    else if i.val = bitWidth k
    then writeBit
    else dir == Dir.R

-- The truth table for δ: maps input bits to output bits
def tmTruthTable {k : ℕ} (hk : 0 < k)
    (δ : TMTransition k)
    (outBit : Fin (tmOutputWidth k)) :
    (Fin (tmInputWidth k) → Bool) → Bool :=
  fun inputBits =>
    -- decode state from input bits
    let stateVal := bitsToNat (bitWidth k)
      (fun i => inputBits ⟨i.val, by simp [tmInputWidth]; omega⟩)
    let sym := inputBits ⟨tmInputWidth k - 1,
      by simp [tmInputWidth]; omega⟩
    if h : stateVal < k then
      let (newState, writeBit, dir) := δ ⟨stateVal, h⟩ sym
      tmOutputBits newState writeBit dir outBit
    else
      false

-- Build circuit encoding using DNF
def buildTMCircuitEncoding {k : ℕ} (hk : 0 < k)
    (δ : TMTransition k) :
    Fin (tmOutputWidth k) →
    (Fin (tmInputWidth k) → Bool) → Bool :=
  fun outBit inputBits =>
    dnf (tmInputWidth k) (tmTruthTable hk δ outBit) inputBits

-- Core correctness: DNF computes the truth table
-- so buildTMCircuitEncoding matches δ
theorem buildTMCircuitEncoding_correct {k : ℕ} (hk : 0 < k)
    (δ : TMTransition k) (state : Fin k) (sym : Bool) :
    let inputBits := tmInputBits state sym
    let (newState, writeBit, dir) := δ state sym
    -- write bit correct
    buildTMCircuitEncoding hk δ
      ⟨bitWidth k, by simp [tmOutputWidth]; omega⟩
      inputBits = writeBit ∧
    -- direction bit correct
    buildTMCircuitEncoding hk δ
      ⟨bitWidth k + 1, by simp [tmOutputWidth]; omega⟩
      inputBits = (dir == Dir.R) ∧
    -- new state bits correct
    ∀ (i : Fin (bitWidth k)),
      buildTMCircuitEncoding hk δ
        ⟨i.val, by simp [tmOutputWidth]; omega⟩
        inputBits =
      natToBits newState.val (bitWidth k) i := by
  intro inputBits
  simp [buildTMCircuitEncoding]
  -- DNF correctness reduces this to truth table correctness
  constructor
  · rw [dnf_correct]
    simp [tmTruthTable, inputBits, tmInputBits]
    -- bitsToNat (natToBits state.val) = state.val
    rw [bitsToNat_natToBits (bitWidth k) state.val
      (bitWidth_spec state.val (Nat.pos_of_ne_zero (by omega)))]
    simp [tmOutputBits]
  constructor
  · rw [dnf_correct]
    simp [tmTruthTable, inputBits, tmInputBits]
    rw [bitsToNat_natToBits (bitWidth k) state.val
      (bitWidth_spec state.val (Nat.pos_of_ne_zero (by omega)))]
    simp [tmOutputBits, tmOutputWidth]
  · intro i
    rw [dnf_correct]
    simp [tmTruthTable, inputBits, tmInputBits]
    rw [bitsToNat_natToBits (bitWidth k) state.val
      (bitWidth_spec state.val (Nat.pos_of_ne_zero (by omega)))]
    simp [tmOutputBits]

end AgentCompleteness