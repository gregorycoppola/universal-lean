import UniversalLean.AgentCompleteness.TMCorrectness

namespace AgentCompleteness

-- A concrete 2-state, 2-symbol TM
-- This is a simple "flip all bits and move right" machine
-- State 0: flip bit, move right, stay in state 0
-- State 1: halt (identity)

def flipTM : TMTransition 2 :=
  fun state sym =>
    match state.val with
    | 0 => (⟨0, by omega⟩, !sym, Dir.R)  -- flip and move right
    | _ => (⟨1, by omega⟩, sym,  Dir.R)  -- halt state

-- Initial config: all zeros tape, head at 0, state 0
def flipInitConfig (tapeLen : ℕ) (hL : 0 < tapeLen) : TMConfig 2 tapeLen :=
  { state := ⟨0, by omega⟩
    tape  := fun _ => false
    head  := ⟨0, hL⟩ }

-- After tapeLen steps, all bits should be flipped
-- (sorry'd: needs induction over tape positions)
lemma flipTM_flips_all {tapeLen : ℕ} (hL : 0 < tapeLen) (i : Fin tapeLen) :
    (tmRun flipTM (flipInitConfig tapeLen hL) tapeLen hL).tape i = true := by
  sorry

-- Corollary: forwardPass correctly simulates flipTM
theorem flipTM_circuit_correct {tapeLen depth : ℕ}
    (hL : 0 < tapeLen) (hd : 0 < depth)
    (i : Fin tapeLen) :
    decodeTape
      (forwardPass^[tapeLen]
        (encode (by omega : 0 < 2) hd (flipInitConfig tapeLen hL))) i
    = true := by
  rw [tm_correctness (by omega) hd hL flipTM]
  exact flipTM_flips_all hL i

end AgentCompleteness