namespace AgentCompleteness

inductive GateType
  | AND | OR | NOT | NAND | NOR | XOR | COPY
  deriving Repr, DecidableEq

structure Token (n : ℕ) where
  val      : Bool
  pos      : Fin n
  gate     : GateType
  wire1    : Fin n
  wire2    : Fin n
  scratch1 : Bool
  scratch2 : Bool
  deriving Repr

def CircuitState (n : ℕ) := Fin n → Token n

end AgentCompleteness