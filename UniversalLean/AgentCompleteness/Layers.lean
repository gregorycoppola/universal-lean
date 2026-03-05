import UniversalLean.AgentCompleteness.Preliminaries

namespace AgentCompleteness

def gatherFirstInput {n : ℕ} (state : CircuitState n) : CircuitState n :=
  fun j =>
    let tok := state j
    let src := state tok.wire1
    { tok with scratch1 := src.val }

def gatherSecondInput {n : ℕ} (state : CircuitState n) : CircuitState n :=
  fun j =>
    let tok := state j
    let src := state tok.wire2
    { tok with scratch2 := src.val }

def applyGate (g : GateType) (a b : Bool) : Bool :=
  match g with
  | GateType.AND  => a && b
  | GateType.OR   => a || b
  | GateType.NOT  => !a
  | GateType.NAND => !(a && b)
  | GateType.NOR  => !(a || b)
  | GateType.XOR  => (a || b) && !(a && b)
  | GateType.COPY => a

def computeGate {n : ℕ} (state : CircuitState n) : CircuitState n :=
  fun j =>
    let tok := state j
    { tok with val := applyGate tok.gate tok.scratch1 tok.scratch2 }

-- Layer 4 is sorry'd: requires program token / iteration counter machinery
def updateWiring {n : ℕ} (state : CircuitState n) : CircuitState n := by
  exact state  -- identity for now, real impl needs program tokens

def forwardPass {n : ℕ} (state : CircuitState n) : CircuitState n :=
  updateWiring (computeGate (gatherSecondInput (gatherFirstInput state)))

end AgentCompleteness
