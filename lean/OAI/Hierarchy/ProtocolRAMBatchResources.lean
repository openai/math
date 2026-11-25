import OAI.Hierarchy.ProtocolRAMBatch

namespace OAI
/-! # Uniform work of a native row program over fixed finite operand families -/

namespace Hierarchy.ProtocolRAM.RowResources
open ThreeFlat.RAM.DescriptorExpr
open scoped Classical

/-- Bounds instruction work simultaneously across word sizes, physical base addresses
and the input-dependent words stored at those addresses. -/
def Bounded {I : Type*} (e : I→Expr) : Prop := ∃C : ℕ, ∀i,(e i).work≤C

variable {I : Type*}

theorem row : Bounded (fun _ : I=>Expr.row) := ⟨2,fun _=>le_rfl⟩
theorem lit (n : I→ℕ) : Bounded (fun i=>Expr.lit (n i)) := ⟨1,fun _=>le_rfl⟩

theorem load (b : I→Bank) {a : I→Expr} (h : Bounded a) :
    Bounded (fun i=>Expr.lookup (b i) (a i)) := by
  obtain ⟨c,h⟩:=h
  exact ⟨c+5,fun i=>Nat.add_le_add_right (h i) 5⟩

theorem op (o : I→RowOp) {x y : I→Expr} (hx : Bounded x) (hy : Bounded y) :
    Bounded (fun i=>Expr.op (o i) (x i) (y i)) := by
  obtain ⟨s,hs⟩:=hx
  obtain ⟨t,ht⟩:=hy
  exact ⟨s+t+1,fun i=>Nat.add_le_add_right (Nat.add_le_add (hs i) (ht i)) 1⟩

theorem branch (o : I → Comparison) {x y a b : I→Expr} (hx : Bounded x) (hy : Bounded y)
    (ha : Bounded a) (hb : Bounded b) : Bounded (fun i=>Expr.branch (o i) (x i) (y i) (a i) (b i)) := by
  obtain ⟨sx,hx⟩:=hx
  obtain ⟨sy,hy⟩:=hy
  obtain ⟨sa,ha⟩:=ha
  obtain ⟨sb,hb⟩:=hb
  exact ⟨sx+sy+sa+sb+1,fun i=>Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hx i) (hy i)) (ha i)) (hb i)) 1⟩

theorem ite (p : I→Prop) [DecidablePred p] {a b : I→Expr} (ha : Bounded a) (hb : Bounded b) :
    Bounded (fun i=>if p i then a i else b i) := by
  obtain ⟨x,hx⟩:=ha
  obtain ⟨y,hy⟩:=hb
  refine ⟨max x y,fun i=>?_⟩
  by_cases h : p i
  · simpa only [h,ite_true] using (hx i).trans (le_max_left x y)
  · simpa only [h,ite_false] using (hy i).trans (le_max_right x y)

theorem scale (n : ℕ) {e : I→Expr} (small : Bounded e) :
    Bounded (fun i=>ProtocolRAM.scale n (e i)) := by
  induction n with
  | zero => exact lit _
  | succ n ih => exact op _ small ih

theorem product (n : ℕ) {x coeff : I→Expr} (hx : Bounded x) (hc : Bounded coeff) :
    Bounded (fun i=>boundedMul n (x i) (coeff i)) := by
  induction n with
  | zero => exact lit _
  | succ n ih => exact branch (fun _=>.eq) hc (lit (fun _=>n+1)) (scale (n+1) hx) ih

theorem sum (n : ℕ) (f : I→Fin n→Expr) (h : ∀j,Bounded (fun i=>f i j)) :
    Bounded (fun i=>totals n (f i)) := by
  induction n with
  | zero => exact lit _
  | succ n ih => exact op _ (h 0) (ih (fun i j=>f i j.succ) (fun j=>h j.succ))

theorem enough (n : ℕ) (a b : I→Fin n→Expr) {x y : I→Expr}
    (ha : ∀j,Bounded (fun i=>a i j)) (hb : ∀j,Bounded (fun i=>b i j))
    (hx : Bounded x) (hy : Bounded y) : Bounded (fun i=>ifEnough n (a i) (b i) (x i) (y i)) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    exact branch (fun _=>.lt) (hb 0) (ha 0) hy
      (ih (fun i j=>a i j.succ) (fun i j=>b i j.succ) (fun j=>ha j.succ) (fun j=>hb j.succ))

theorem counts (n : ℕ) (t : I→ℕ) (f : I→Fin n→Expr) {x y : I→Expr}
    (h : ∀j,Bounded (fun i=>f i j)) (hx : Bounded x) (hy : Bounded y) :
    Bounded (fun i=>ifHistogram n (t i) (f i) (x i) (y i)) :=
  enough n f (fun i _=>.lit (t i)) h (fun _=>lit t) (branch (fun _=>.eq) (sum n f h) (lit t) hx hy) hy

structure BatchOperands {q d : ℕ} (b : I→Batch q d) (maximum : ℕ) : Prop where
  coeff : ∀i,(b i).maxWidth=maximum
  packet : Bounded (fun i=>(b i).packet)
  owner : Bounded (fun i=>(b i).owner)
  field : ∀j,Bounded (fun i=>(b i).field j)
  stock : ∀j,Bounded (fun i=>(b i).stock j)
  perCopy : ∀j,Bounded (fun i=>(b i).perCopy j)

variable {q d maximum : ℕ} {b : I→Batch q d} (v : BatchOperands b maximum)
include v

theorem BatchOperands.need (j : Fin d) : Bounded (fun i=>(b i).need j) := by
  simpa only [Batch.need,v.coeff] using product maximum (lit (fun i=>(b i).copies)) (v.perCopy j)

theorem BatchOperands.selection {yes no : I→Expr} (hy : Bounded yes) (hn : Bounded no) :
    Bounded (fun i=>(b i).ifSelected (yes i) (no i)) :=
  branch (fun _=>.eq) (load (fun i=>(b i).enabled) v.owner) (lit (fun _=>0)) hn
    (branch (fun _=>.eq) v.packet (lit (fun _=>0)) hn (enough _ _ _ v.need v.stock hy hn))

theorem BatchOperands.hist {yes no : I→Expr} (hy : Bounded yes) (hn : Bounded no) :
    Bounded (fun i=>(b i).ifPacket (yes i) (no i)) :=
  enough _ _ _ v.field (fun j=>branch (fun _=>.lt) (lit (fun _=>j.val))
    (load (fun i=>(b i).termCount) v.packet) (lit (fun i=>(b i).copies)) (lit (fun _=>0)))
    (counts _ _ _ v.field hy hn) hn

theorem BatchOperands.valid {yes no : I→Expr} (hy : Bounded yes) (hn : Bounded no) :
    Bounded (fun i=>(b i).ifAdmitted (yes i) (no i)) :=
  v.selection (v.hist hy hn) (counts _ _ _ v.field hy hn)

theorem BatchOperands.width (tab : I→Fin q→Expr) (ht : ∀j,Bounded (fun i=>tab i j)) :
    Bounded (fun i=>(b i).wire (tab i)) := by
  apply v.selection _ (lit _)
  apply v.hist _ (lit _)
  unfold installed
  apply sum q
  intro j
  simpa only [v.coeff] using product maximum (v.field j) (ht j)

theorem BatchOperands.updated {credit : I→Expr} (j : Fin d) (hc : Bounded credit) :
    Bounded (fun i=>(b i).nextStock j (credit i)) :=
  v.selection (v.hist (op _ (op _ (v.stock j) (v.need j)) hc) (v.stock j)) (v.stock j)

end Hierarchy.ProtocolRAM.RowResources

end OAI
