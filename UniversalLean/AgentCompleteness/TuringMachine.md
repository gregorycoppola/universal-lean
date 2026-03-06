# TuringMachine.lean — The Turing Machine Model

This file defines the Turing machine model that the transformer is proved
to simulate. It specifies configurations, the transition function type,
single-step execution, and iterated execution.

## Design Choices

The TM model is kept minimal: a single tape, two-way head movement,
finitely many states indexed by Fin k. The tape is finite but parameterized
by tapeLen, with the proof working for any tapeLen. The halting condition
is not modelled — we prove that d steps of the TM correspond to d forward
passes of the transformer for any d, which is the content of Turing completeness.

## Key Types

Dir — An inductive type with two constructors: L (move left) and R (move right).
Specifies which direction the head moves after each transition.

TMConfig k tapeLen — A structure representing a complete TM configuration:

  tape : Fin tapeLen -> Bool — the contents of the tape. A function from
  position index to Boolean value. Using a function rather than a list
  simplifies updates: the new tape after a write is just a function that
  returns the written value at the head position and the old value elsewhere.

  head : Fin tapeLen — the current head position, bounded by tapeLen.
  Using Fin ensures the head is always a valid tape position.

  state : Fin k — the current machine state, one of k states indexed
  from 0 to k-1.

TMTransition k — The type of transition functions: Fin k -> Bool -> (Fin k, Bool, Dir).
Takes a state and a tape symbol, returns a new state, a symbol to write,
and a direction to move. This is a total function — every (state, symbol)
pair has a defined transition.

## Key Functions

tmStep delta cfg hL — Applies one step of the TM. Given a transition function
delta, a configuration cfg, and a proof hL that tapeLen > 0 (needed to
ensure head movement stays in bounds), computes the next configuration.

The new tape writes the output symbol at the head position and preserves
all other cells. Formally: new_tape[i] = if i = cfg.head then writeBit else cfg.tape[i].

The new head position moves left or right from cfg.head, wrapping or
clamping at the tape boundaries (depending on the implementation).
The proof hL ensures this movement produces a valid Fin tapeLen.

The new state is newState from delta(cfg.state, cfg.tape[cfg.head]).

tmRun delta cfg d hL — Applies tmStep d times starting from cfg.
Defined by recursion on d: tmRun d=0 returns cfg unchanged,
tmRun (d+1) returns tmStep applied to tmRun d.

This gives the configuration after exactly d steps of execution.
The tape of tmRun(delta, cfg, d) is what the transformer must produce
after d forward passes to count as simulating the TM.

## Role in the Proof

TuringMachine.lean is imported by Encoding.lean, ProgramEncoding.lean,
TMCorrectness.lean, and TuringComplete.lean.

The simulation theorem forwardPass_iter_simulates_tmRun in TMCorrectness.lean
states that for any WellFormed initial state encoding cfg,
decodeTape(forwardPass^d(state0)) = tmRun(delta, cfg, d).tape.

This is proved by induction on d, using tmStep at each inductive step
and wellFormed_preserved to carry the invariant forward.

The choice to use Fin k for states and Fin tapeLen for the head position
is important for the formalization: it ensures all indexing is automatically
bounds-checked by Lean's type system, eliminating a large class of potential
proof obligations about out-of-bounds access.