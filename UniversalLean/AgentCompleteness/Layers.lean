import UniversalLean.AgentCompleteness.Preliminaries

namespace AgentCompleteness

-- Layer 1: gather first input value into scratch1
def gatherFirstInput {n depth : ℕ} (state : CircuitState n depth) : CircuitState n depth :=
  fun j =>
    let tok := state j
    let src := state tok.wire1
    { tok with scratch1 := src.val }

-- Layer 2: gather second input value into scratch2
def gatherSecondInput {n depth : ℕ} (state : CircuitState n depth) : CircuitState n depth :=
  fun j =>
    let tok := state j
    let src := state tok.wire2
    { tok with scratch2 := src.val }

-- Gate computation
def applyGate (g : GateType) (a b : Bool) : Bool :=
  match g with
  | GateType.AND  => a && b
  | GateType.OR   => a || b
  | GateType.NOT  => !a
  | GateType.NAND => !(a && b)
  | GateType.NOR  => !(a || b)
  | GateType.XOR  => (a || b) && !(a && b)
  | GateType.COPY => a

-- Layer 3: compute gate function from scratch registers
def computeGate {n depth : ℕ} (state : CircuitState n depth) : CircuitState n depth :=
  fun j =>
    let tok := state j
    { tok with val := applyGate tok.gate tok.scratch1 tok.scratch2 }

-- Layer 4: real updateWiring
-- reads next layer's wiring from program tokens and advances iteration counter
def updateWiring {n depth : ℕ} (state : CircuitState n depth) : CircuitState n depth :=
  fun j =>
    let tok := state j
    -- get wiring for next iteration if available
    let nextIter : Fin depth := tok.iteration
    let wiring := tok.program nextIter j
    { tok with
      wire1 := wiring.wire1
      wire2 := wiring.wire2 }

-- One full forward pass
def forwardPass {n depth : ℕ} (state : CircuitState n depth) : CircuitState n depth :=
  updateWiring (computeGate (gatherSecondInput (gatherFirstInput state)))

-- Advance iteration counter (separate step, called by agent loop)
def advanceIteration {n depth : ℕ} (state : CircuitState n depth)
    (hlt : ∀ j, (state j).iteration.val + 1 < depth) : CircuitState n depth :=
  fun j =>
    let tok := state j
    { tok with iteration := ⟨tok.iteration.val + 1, hlt j⟩ }

end AgentCompleteness