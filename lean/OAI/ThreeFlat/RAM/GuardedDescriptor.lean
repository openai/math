import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # A native ROM expression for one word of a guarded block network

A block has the copied tensor cells followed by the boundary equality cells.
Each cell occupies eleven words, first three sources then its coefficient
table. The four supplied lookups receive the current block as their first
argument. The copied word is evaluated once and bound to a register.
-/

namespace ThreeFlat.RAM.GuardedDescriptor

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr

structure Inputs (α : Type*) where
  address : α
  cellsBase : α
  oldPins : α
  oldCells : α
  oldHidden : α
  guards : α
  globalPins : α
  shared : α
  zeroCode : α
  unitCode : α

def Inputs.map {α β : Type*} (f : α → β) (p : Inputs α) : Inputs β :=
  ⟨f p.address,f p.cellsBase,f p.oldPins,f p.oldCells,f p.oldHidden,f p.guards,
    f p.globalPins,f p.shared,f p.zeroCode,f p.unitCode⟩

structure Ops (α : Type*) where
  lit : ℕ → α
  bin : BinaryOp → α → α → α
  sel : Comparison → α → α → α → α → α

structure Coordinates (α : Type*) where
  block : α
  localCell : α
  col : α
  guardIndex : α

def coordinates {α : Type*} (s : Ops α) (p : Inputs α) : Coordinates α :=
  let off := s.bin .sub p.address p.cellsBase
  let cell := s.bin .div off (s.lit 11)
  let width := s.bin .add p.oldCells p.guards
  let b := s.bin .div cell width
  let i := s.bin .mod cell width
  ⟨b,i,s.bin .mod off (s.lit 11),s.bin .sub i p.oldCells⟩

def finish {α : Type*} (s : Ops α) (p : Inputs α) (c : Coordinates α)
    (raw pin left right : α) : α :=
  let start := s.bin .add (s.lit 2) p.oldPins
  let base := s.bin .add (s.bin .add (s.lit 2) p.globalPins) p.shared
  let hidden := s.bin .add (s.bin .add base (s.bin .mul c.block p.oldHidden)) (s.bin .sub raw start)
  let source := s.sel .lt raw (s.lit 2) raw (s.sel .lt raw start pin hidden)
  let u := s.bin .sub c.col (s.lit 3)
  let x := s.bin .mod u (s.lit 2)
  let y := s.bin .mod (s.bin .div u (s.lit 2)) (s.lit 2)
  let coeff := s.sel .eq x y p.unitCode p.zeroCode
  let guard := s.sel .eq c.col (s.lit 0) left
    (s.sel .eq c.col (s.lit 1) right (s.sel .eq c.col (s.lit 2) (s.lit 0) coeff))
  s.sel .lt c.localCell p.oldCells (s.sel .lt c.col (s.lit 3) source raw) guard

variable {w k n : ℕ}

def wordOps (w : ℕ) : Ops (Word w) :=
  ⟨Fin.ofNat _, BinaryOp.eval, fun cmp a b yes no => if cmp.test a b then yes else no⟩

private def termOps (w k n : ℕ) : Ops (Term w k n) :=
  ⟨fun j => .literal (Fin.ofNat _ j), Term.binary, Term.select⟩

/-- The specified word calculation. A mapped pin or guard endpoint is supplied
as its full binary source code in the new memory. All arithmetic is native
unsigned word arithmetic. -/
def word (p : Inputs (Word w)) (copy : Word w → Word w → Word w → Word w)
    (pin left right : Word w → Word w → Word w) : Word w :=
  let s := wordOps w
  let c := coordinates s p
  let raw := copy c.block c.localCell c.col
  finish s p c raw (pin c.block (s.bin .sub raw (s.lit 2))) (left c.block c.guardIndex)
    (right c.block c.guardIndex)

/-- The copied cell reader sees column, local cell, block, then the original
input words in its register environment. Each pair lookup sees index, block,
then the original inputs. -/
structure Lookups (w k n : ℕ) where
  copy : Term w k (n+3)
  pin : Term w k (n+2)
  left : Term w k (n+2)
  right : Term w k (n+2)

private def call3 (a b c : Term w k n) (f : Term w k (n+3)) : Term w k n :=
  a.letThen ((b.rename Fin.succ).letThen ((c.rename (fun i => i.succ.succ)).letThen f))

private def call2 {d : ℕ} (ρ : Fin n → Fin d) (a b : Term w k d) (f : Term w k (n+2)) :
    Term w k d :=
  a.letThen ((b.rename Fin.succ).letThen
    (f.rename (Fin.cons 0 (Fin.cons (Fin.succ 0) (fun i => (ρ i).succ.succ)))))

/-- Instantiate the guarded descriptor expression. Register assignments for the
ten input parameters may refer to any of the caller's words. -/
def compile (p : Inputs (Fin n)) (L : Lookups w k n) : Term w k n :=
  let c := coordinates (termOps w k n) (p.map Term.result)
  let raw := call3 c.block c.localCell c.col L.copy
  let s := termOps w k (n+1)
  let p' := p.map (fun i => (Term.result i.succ : Term w k (n+1)))
  let d := coordinates s p'
  let v : Term w k (n+1) := .result 0
  raw.letThen (finish s p' d v (call2 Fin.succ d.block (s.bin .sub v (s.lit 2)) L.pin)
    (call2 Fin.succ d.block d.guardIndex L.left) (call2 Fin.succ d.block d.guardIndex L.right))

private theorem eval_call3 (a b c : Term w k n) (f : Term w k (n+3))
    (data : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w) :
    (call3 a b c f).eval data m vs = f.eval data m
      (Fin.cons (c.eval data m vs) (Fin.cons (b.eval data m vs) (Fin.cons (a.eval data m vs) vs))) := by
  simp [call3,Function.comp_def]

private theorem eval_call2 {d : ℕ} (ρ : Fin n → Fin d) (a b : Term w k d) (f : Term w k (n+2))
    (data : Fin k → Word w) (m : Memory w) (vs : Fin d → Word w) :
    (call2 ρ a b f).eval data m vs = f.eval data m
      (Fin.cons (b.eval data m vs) (Fin.cons (a.eval data m vs) (vs ∘ ρ))) := by
  simp only [call2, Term.eval_letThen, Term.eval_rename]
  have tail (v : Word w) : Fin.cons v vs ∘ Fin.succ = vs := by funext j; simp
  rw [tail]
  apply congrArg (f.eval data m)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · refine Fin.cases ?_ (fun _ => ?_) j <;> simp

/-- Correctness of the word read, including transport of copied pin and hidden
sources and the two source words and eight coefficients of an equality guard. -/
theorem eval_compile (p : Inputs (Fin n)) (L : Lookups w k n) (data : Fin k → Word w)
    (m : Memory w) (vs : Fin n → Word w) :
    (compile p L).eval data m vs = word (p.map vs)
      (fun block i col => L.copy.eval data m (Fin.cons col (Fin.cons i (Fin.cons block vs))))
      (fun block i => L.pin.eval data m (Fin.cons i (Fin.cons block vs)))
      (fun block i => L.left.eval data m (Fin.cons i (Fin.cons block vs)))
      (fun block i => L.right.eval data m (Fin.cons i (Fin.cons block vs))) := by
  simp [compile,word,coordinates,finish,termOps,wordOps,Inputs.map,eval_call3,eval_call2,
    Term.eval,Function.comp_def]

/-- The four child expressions occur once each. The fixed overhead also covers
the row-major address arithmetic, including computations for unused choices. -/
theorem binds_compile (p : Inputs (Fin n)) (L : Lookups w k n) :
    (compile p L).binds = L.copy.binds + L.pin.binds + L.left.binds + L.right.binds + 105 := by
  simp [compile,coordinates,finish,termOps,Inputs.map,call3,call2,
    Term.binary,Term.select,Term.literal,Term.binds]
  omega

theorem steps_compile_le (p : Inputs (Fin n)) (L : Lookups w k n) :
    (compile p L).steps ≤ L.copy.steps + L.pin.steps + L.left.steps + L.right.steps + 207 := by
  have := binds_compile p L
  simp only [Term.steps_eq]
  omega

/-- A descriptor taking only the absolute address in its input register. Supply
the other source values as constants or machine public-word loads in `args`. -/
def bindParams (p : Inputs (Fin n)) (L : Lookups w k n) (args : Fin n → Term w k 1) :
    Term w k 1 := (compile p L).instantiate args

theorem binds_bindParams (p : Inputs (Fin n)) (L : Lookups w k n)
    (args : Fin n → Term w k 1) :
    (bindParams p L args).binds = (compile p L).binds + ∑ i, (args i).binds := by
  simp [bindParams]

end ThreeFlat.RAM.GuardedDescriptor

end OAI
