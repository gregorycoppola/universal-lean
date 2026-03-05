import UniversalLean.AgentCompleteness.Preliminaries

namespace AgentCompleteness

noncomputable def relu (x : ℝ) : ℝ := max 0 x

noncomputable def boolAnd  (a b : ℝ) : ℝ := relu (a + b - 1.5) / 0.5
noncomputable def boolOr   (a b : ℝ) : ℝ := relu (a + b - 0.5) - relu (a + b - 1.5)
noncomputable def boolNot  (a : ℝ)   : ℝ := 1 - a
noncomputable def boolNand (a b : ℝ) : ℝ := 1 - boolAnd a b
noncomputable def boolXor  (a b : ℝ) : ℝ := boolOr a b - boolAnd a b
noncomputable def boolCopy (a : ℝ)   : ℝ := a

-- Lemma 4.3
lemma and_00 : boolAnd 0 0 = 0 := by simp [boolAnd, relu]
lemma and_01 : boolAnd 0 1 = 0 := by simp [boolAnd, relu]
lemma and_10 : boolAnd 1 0 = 0 := by simp [boolAnd, relu]
lemma and_11 : boolAnd 1 1 = 1 := by norm_num [boolAnd, relu]

lemma or_00 : boolOr 0 0 = 0 := by simp [boolOr, relu]
lemma or_01 : boolOr 0 1 = 1 := by norm_num [boolOr, relu]
lemma or_10 : boolOr 1 0 = 1 := by norm_num [boolOr, relu]
lemma or_11 : boolOr 1 1 = 1 := by norm_num [boolOr, relu]

lemma not_0 : boolNot 0 = 1 := by simp [boolNot]
lemma not_1 : boolNot 1 = 0 := by simp [boolNot]

end AgentCompleteness