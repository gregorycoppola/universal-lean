import UniversalLean.AgentCompleteness.Preliminaries

namespace AgentCompleteness

-- A simple 2-symbol Turing machine
-- States are Fin k for some k, symbols are Bool (0/1)
-- Tape is finite, represented as an array of Bool

structure TMConfig (k tapeLen : ℕ) where
  state    : Fin k          -- current machine state
  tape     : Fin tapeLen → Bool  -- tape contents
  head     : Fin tapeLen    -- head position
  deriving Repr

-- Direction: move left or right
inductive Dir | L | R deriving Repr, DecidableEq

-- Transition function: given current state and symbol,
-- return new state, symbol to write, and direction to move
def TMTransition (k : ℕ) := Fin k → Bool → (Fin k × Bool × Dir)

-- One step of TM execution
def tmStep {k tapeLen : ℕ}
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (hL : 0 < tapeLen) : TMConfig k tapeLen :=
  let sym := cfg.tape cfg.head
  let (newState, writeSym, dir) := δ cfg.state sym
  -- write symbol to tape
  let newTape := fun i => if i = cfg.head then writeSym else cfg.tape i
  -- move head (clamped to tape bounds)
  let newHead : Fin tapeLen :=
    match dir with
    | Dir.L => if cfg.head.val = 0
               then cfg.head
               else ⟨cfg.head.val - 1, Nat.lt_of_le_of_lt (Nat.pred_le _) cfg.head.isLt⟩
    | Dir.R => if cfg.head.val + 1 < tapeLen
               then ⟨cfg.head.val + 1, by omega⟩
               else cfg.head
  { state := newState, tape := newTape, head := newHead }

-- Run TM for exactly d steps
def tmRun {k tapeLen : ℕ}
    (δ : TMTransition k)
    (cfg : TMConfig k tapeLen)
    (d : ℕ)
    (hL : 0 < tapeLen) : TMConfig k tapeLen :=
  match d with
  | 0     => cfg
  | d + 1 => tmRun δ (tmStep δ cfg hL) d hL

end AgentCompleteness