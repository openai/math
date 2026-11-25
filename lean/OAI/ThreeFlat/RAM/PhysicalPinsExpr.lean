import OAI.ThreeFlat.RAM.GuardedDescriptor

namespace OAI
/-! # Native word code for pin and guard lookups in an aligned block trace

The public words describe the lengths, the location of the public parameter
bits, and the original trace record area. The emitted expressions have fixed
syntax across word widths. Every memory read addresses either a parameter
bit or an offset of the original eleven-word cell array.
-/

namespace ThreeFlat.RAM.PhysicalPinsExpr

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr

/-- Nine shape words and two addresses shared across all blocks. -/
inductive Param where
  | advice | teamBits | timeBits | parameterBits | chunkBits | ticks | teams | period | finalBlock
  | parameterBase | templateBase
  deriving DecidableEq

def Param.index : Param → Fin 11
  | .advice => 0 | .teamBits => 1 | .timeBits => 2 | .parameterBits => 3 | .chunkBits => 4
  | .ticks => 5 | .teams => 6 | .period => 7 | .finalBlock => 8 | .parameterBase => 9
  | .templateBase => 10

/-- A finite formula over public shape words and the few current row operands. -/
inductive Formula (n : ℕ) where
  | reg (i : Fin n)
  | lit (a : ℕ)
  | param (i : Param)
  | op (b : BinaryOp) (x y : Formula n)
  | cut (x y : Formula n)
  | load (x : Formula n)
  | select (q : Comparison) (x y yes no : Formula n)

variable {n k w : ℕ}

def Formula.compile (param : Param → Fin k) : Formula n → Term w k n
  | .reg i => .result i
  | .lit a => .literal (Fin.ofNat _ a)
  | .param i => .parameter (param i)
  | .op b x y => .binary b (x.compile param) (y.compile param)
  | .cut x y => .select .lt (x.compile param) (y.compile param) (.literal 0)
      (.binary .sub (x.compile param) (y.compile param))
  | .load x => .load (x.compile param)
  | .select q x y a b => .select q (x.compile param) (y.compile param) (a.compile param) (b.compile param)

def Formula.value (data : Param → Word w) (mem : Memory w) (vs : Fin n → Word w) :
    Formula n → Word w
  | .reg i => vs i
  | .lit a => Fin.ofNat _ a
  | .param i => data i
  | .op b x y => b.eval (x.value data mem vs) (y.value data mem vs)
  | .cut x y => if Comparison.test .lt (x.value data mem vs) (y.value data mem vs) then 0
      else BinaryOp.eval .sub (x.value data mem vs) (y.value data mem vs)
  | .load x => mem (x.value data mem vs).val
  | .select q x y a b => if q.test (x.value data mem vs) (y.value data mem vs)
      then a.value data mem vs else b.value data mem vs

theorem Formula.eval_compile (p : Param → Fin k) (f : Formula n) (data : Fin k → Word w)
    (mem : Memory w) (vs : Fin n → Word w) :
    (f.compile p).eval data mem vs = f.value (data ∘ p) mem vs := by
  induction f <;> simp [Formula.compile, Term.eval, Formula.value, *]

/-- Exact number of let-bound instructions in the compiled formula. -/
def Formula.work : Formula n → ℕ
  | .reg _ => 0
  | .lit _ | .param _ => 1
  | .op _ x y => x.work+y.work+1
  | .cut x y => 2*x.work+2*y.work+3
  | .load x => x.work+1
  | .select _ x y a b => x.work+y.work+a.work+b.work+1

theorem Formula.binds_compile (p : Param → Fin k) (f : Formula n) :
    ((f.compile p : Term w k n)).binds = f.work := by
  induction f <;> simp [Formula.compile, Formula.work, Term.literal, Term.parameter, Term.binary,
    Term.select, Term.load, Term.binds, *] <;> omega

abbrev A := @Formula.param n
abbrev L := @Formula.lit n
abbrev add := @Formula.op n .add
abbrev sub := @Formula.cut n
abbrev mul := @Formula.op n .mul
abbrev div := @Formula.op n .div
abbrev rem := @Formula.op n .mod
abbrev eqz := @Formula.select n .eq
abbrev lt := @Formula.select n .lt

def half : Formula n := mul (mul (A .period) (A .ticks)) (A .chunkBits)
def state : Formula n := add (mul (L 2) half) (A .chunkBits)
def hiddenStart : Formula n := add (L 2) (add (A .advice) (mul (L 2) state))

def endpoint (right : Bool) (block pos : Formula n) : Formula n :=
  let pub := add (add (L 2) (A .advice)) pos
  if right then eqz block (A .finalBlock) (add pub state) (add (add hiddenStart (mul block state)) pos)
  else eqz block (L 0) pub (add (add hiddenStart (mul (sub block (L 1)) state)) pos)

def middle (block tick bit : Formula n) : Formula n :=
  add (add (add (add hiddenStart (mul (A .finalBlock) state))
    (mul block (mul (sub (A .ticks) (L 1)) (A .chunkBits)))) (mul tick (A .chunkBits))) bit

def active (block : Formula n) : Formula n := rem (div block (A .period)) (L 2)

def guardFormula (right : Bool) (block raw : Formula n) : Formula n :=
  eqz (div (div raw (A .chunkBits)) (A .ticks)) (rem block (A .period)) (L 0)
    (endpoint right block (add (mul (active block) half) raw))

/-- Resolve all tick and catalyst fields at a raw pin index of the collapsed network. -/
def pinFormula (block raw : Formula n) : Formula n :=
  let z0 := A .advice
  let z1 := add z0 (A .teamBits)
  let z2 := add z1 (A .timeBits)
  let z3 := add z2 (A .parameterBits)
  let z4 := add z3 (A .chunkBits)
  let z5 := add z4 (A .chunkBits)
  let z6 := add z5 (A .chunkBits)
  let plen := add z6 (A .chunkBits)
  let area := mul (mul (A .ticks) (A .teams)) plen
  let which := div raw plen
  let tick := div which (A .teams)
  let team := rem which (A .teams)
  let j := rem raw plen
  let numberBit (value bit : Formula n) := rem (.op .shiftRight value bit) (L 2)
  let oldAux (bit : Formula n) := eqz tick (L 0) (endpoint false block (add (mul (L 2) half) bit))
    (middle block (sub tick (L 1)) bit)
  let newAux (bit : Formula n) := eqz tick (sub (A .ticks) (L 1))
    (endpoint true block (add (mul (L 2) half) bit)) (middle block tick bit)
  let chunk := add (mul (rem block (A .period)) (A .ticks)) tick
  let chunkPos (bit : Formula n) := add (add (mul (active block) half) (mul chunk (A .chunkBits))) bit
  let field := lt j z0 (add (L 2) j)
    (lt j z1 (numberBit team (sub j z0))
    (lt j z2 (numberBit (add (mul block (A .ticks)) tick) (sub j z1))
    (lt j z3 (.load (add (A .parameterBase) (sub j z2)))
    (lt j z4 (oldAux (sub j z3))
    (lt j z5 (newAux (sub j z4))
    (lt j z6 (endpoint false block (chunkPos (sub j z5)))
      (endpoint true block (chunkPos (sub j z6)))))))))
  let off := sub raw area
  let pos := add (mul (sub (L 1) (active block)) half) (rem off half)
  lt raw area field (lt off half (endpoint false block pos) (endpoint true block pos))

/-- Read one of the eleven words in a row of the original X trace. -/
def copyFormula (localCell col : Formula n) : Formula n :=
  .load (add (add (A .templateBase) (mul (L 11) localCell)) col)

/-- The descriptor callbacks run on column/local-cell/block or index/block,
followed by the caller's already-bound shape words. -/
def lookups (p : Param → Fin k) : GuardedDescriptor.Lookups w k n where
  copy := (copyFormula (.reg 1) (.reg 0)).compile p
  pin := (pinFormula (.reg 1) (.reg 0)).compile p
  left := (guardFormula false (.reg 1) (.reg 0)).compile p
  right := (guardFormula true (.reg 1) (.reg 0)).compile p

end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
