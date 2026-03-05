namespace AgentCompleteness

inductive GateType
  | AND | OR | NOT | NAND | NOR | XOR | COPY
  deriving Repr, DecidableEq

-- Wiring for one gate: its two input positions
structure GateWiring (n : ℕ) where
  wire1 : Fin n
  wire2 : Fin n
  deriving Repr

-- Program: wiring for all gates across all layers
-- program[layer][gate] = wiring for that gate at that layer
def Program (n depth : ℕ) := Fin depth → Fin n → GateWiring n

structure Token (n depth : ℕ) where
  val       : Bool           -- current bit value
  pos       : Fin n          -- position in circuit
  gate      : GateType       -- gate type (fixed across layers)
  wire1     : Fin n          -- current layer's first input
  wire2     : Fin n          -- current layer's second input
  scratch1  : Bool           -- gathered first input value
  scratch2  : Bool           -- gathered second input value
  iteration : Fin depth      -- which layer we are on
  program   : Program n depth  -- full wiring for all layers
  deriving Repr

def CircuitState (n depth : ℕ) := Fin n → Token n depth

end AgentCompleteness