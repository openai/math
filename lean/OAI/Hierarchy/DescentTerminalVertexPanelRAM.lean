import OAI.Hierarchy.DescentTerminalScanReads
import OAI.Hierarchy.DescentTerminalSumExpr
import OAI.Hierarchy.DescentTerminalVertexPanels

namespace OAI
/-! # A single paid scan joins the eight actual primitive shelves at each common position -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalDenseWindow DescentTerminalRowBooks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V W B S bits : ℕ}
local notation "cap" => widthAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V
local notation "width" => span q t H N A w
local notation "Rows" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V

def tablesize := ∏f : Fin 8,2^(cap f)
def stride (f : Fin 8) := ∏i : Fin f.val,2^(cap (i.castLE f.isLt.le))
theorem table_room (h : ℕ) (room : V*width≤h/2) : tablesize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) ≤ 2^(h/2) := by
  unfold tablesize
  rw [Finset.prod_pow_eq_pow_sum,volume]
  exact Nat.pow_le_pow_right (by decide) room

structure Shelf where
  source : Fin 8→Bank
  offset : Fin 8→Bank
  table : Bank

def term (L : Shelf) (f : Fin 8) : Expr := .lookup (L.offset f) (.lookup (L.source f) .row)
def row (L : Shelf) : Expr := .lookup L.table (sumExpr (term L) (List.finRange 8))

def table (fit : V*width≤B) (i : Fin (tablesize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V))) :=
  weave (finPiFinEquiv.symm i : Rows) fit

structure Mounted (L : Shelf) (m : Memory bits) (data : Fin S→Rows) (fit : V*width≤B) : Prop where
  inputs : ∀i f,(L.source f).read m (i.val:Word bits)=((data i f).val:Word bits)
  offset : ∀f,∀n:Word (cap f),(L.offset f).read m (n.val:Word bits)=((n.val*stride (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) f:ℕ):Word bits)
  dictionary : ∀j,L.table.read m (j.val:Word bits)=((table fit j).val:Word bits)

theorem row_by (L : Shelf) (m : Memory bits) (data : Fin S→Rows) (decode : Rows→Word B)
    (inputs : ∀i f,(L.source f).read m (i.val:Word bits)=((data i f).val:Word bits))
    (offsets : ∀f,∀z:Word (cap f),(L.offset f).read m (z.val:Word bits)=((z.val*stride (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) f:ℕ):Word bits))
    (dictionary : ∀j : Fin (tablesize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)),L.table.read m (j.val:Word bits)=((decode (finPiFinEquiv.symm j)).val:Word bits)) (i : Fin S) :
    (row L).eval m (i.val:Word bits)=((decode (data i)).val:Word bits) := by
  let amount:=fun f : Fin 8=>(data i f).val*stride (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) f
  have src (f : Fin 8) : (term L f).eval m (i.val:Word bits)=(amount f:Word bits) := by
    simp [term,Expr.eval,inputs,offsets,amount]
  have key : ((List.finRange 8).map amount).sum=(finPiFinEquiv (data i)).val := by
    rw [finPiFinEquiv_apply]
    change (List.ofFn amount).sum=_
    rw [List.sum_ofFn]
    rfl
  simp only [row,Expr.eval,sum_read (term L) m (i.val:Word bits) amount src,key]
  have loaded := dictionary (finPiFinEquiv (data i))
  simpa only [Equiv.symm_apply_apply] using loaded

theorem row_read (L : Shelf) (m : Memory bits) (data : Fin S→Rows) (fit : V*width≤B) (cols : Mounted L m data fit) (i : Fin S) :
    (row L).eval m (i.val:Word bits)=((weave (data i) fit).val:Word bits) :=
  row_by L m data (fun a=>weave a fit) cols.inputs cols.offset cols.dictionary i

theorem run (L : Shelf) (m : Memory bits) (out : ℕ) (fit : (row L).Fits bits out) (endAt : out+S<2^bits) :
    (scan bits out S (row L)).Exec m (image out S (row L) m) (4+S*(2*(row L).work+4)) ∧ CheapCode (scan bits out S (row L)) :=
  ⟨@scan_exec bits out S (row L) m fit endAt,@scan_cheap _ _ _ _⟩

theorem rows_read (L : Shelf) (m : Memory bits) (data : Fin S→Rows) (fit : V*width≤B) (cols : Mounted L m data fit)
    (out : ℕ) (i : Fin S) : image out S (row L) m (out+i.val)=((weave (data i) fit).val:Word bits) := by
  rw [DescentTerminalDenseHeaderRAM.at_image,row_read L m data fit cols]

theorem row_work (L : Shelf) : (row L).work=110 := rfl

theorem fixed_cost (L : Shelf) : 4+S*(2*(row L).work+4)=4+224*S := by rw [row_work];ring

theorem offset_budget : (∑f : Fin 8,2^(cap f))≤8*tablesize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) := by
  have each (f : Fin 8) : 2^(cap f)≤tablesize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) := by
    unfold tablesize
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (by decide)
      (Finset.single_le_sum (f:=fun i : Fin 8=>cap i) (fun _ _=>Nat.zero_le _) (Finset.mem_univ f))
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>each i)

end
end Hierarchy.DescentTerminalVertexFields

end OAI
