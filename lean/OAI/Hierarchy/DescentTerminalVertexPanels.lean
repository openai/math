import OAI.Hierarchy.DescentTerminalCellCoordinates
import OAI.Hierarchy.DescentTerminalCohortSize
import OAI.Hierarchy.DescentTerminalVertexFieldReads
import OAI.Hierarchy.DescentTerminalPositionFrames
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Interleaving eight small homogeneous terminal panels at each common position -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalRecipeRows DescentTerminalRowBooks DescentTerminalLeafDigits
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V B S : ℕ}
local notation "K" => Key H N A
local notation "len" => bits q t H N A w
local notation "width" => span q t H N A w
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
local notation "extent" => widthAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V
abbrev Panels (V : ℕ) := (f : Fin 8)→Word (widthAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V f)
local notation "Rows" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V

def locate (v : Fin V) (k : K) (j : Fin (len k)) : Fin (extent (group k)) :=
  finProdFinEquiv (v,within k j)

/-- The CPU indexes a fixed little-endian rectangle at every reached position:
node arguments use node ordinal times maximum arity followed by argument number. -/
theorem locate_val (v : Fin V) (k : K) (j : Fin (len k)) :
    (locate v k j).val=(v.val*items H N A (group k)+(item k).val)*itemBits q t H N A w (group k)+j.val := by
  change (j.val+itemBits q t H N A w (group k)*(item k).val)+sized (group k)*v.val=_
  unfold familySize
  ring

def slotOrder : ((k : K)×Fin (len k))≃Fin width :=
  ProtocolRAMPortRanks.enumerate len order order.injective

def weave (panel : Rows) (_fit : V*width≤B) : Word B :=
  (wordBits _).symm fun i=>
    if hi:i.val<V*width then
      let vb:Fin V×Fin width:=finProdFinEquiv.symm ⟨i.val,hi⟩
      let slot:=slotOrder.symm vb.2
      wordBits _ (panel (group slot.1)) (locate vb.1 slot.1 slot.2)
    else false

theorem weave_read (panel : Rows) (fit : V*width≤B) (v : Fin V) (k : K) (j : Fin (len k)) :
    wordBits B (weave panel fit) ((finProdFinEquiv (v,offset k j)).castLE fit)=
      wordBits _ (panel (group k)) (locate v k j) := by
  let z : (i : K)×Fin (len i):=⟨k,j⟩
  let E : ((i : K)×Fin (len i))≃Fin width := slotOrder
  let readAt (r : (i : K)×Fin (len i)) : Bool :=
    wordBits (extent (group r.1)) (panel (group r.1))
      (locate (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) v r.1 r.2)
  have atSlot : offset k j=E z:=rfl
  simp only [weave,Equiv.apply_symm_apply,Fin.val_castLE,(finProdFinEquiv (v,offset k j)).isLt,dite_eq_left]
  change (let slot:=slotOrder.symm ((finProdFinEquiv.symm (finProdFinEquiv (v,offset k j))).2)
    ; wordBits _ (panel (group slot.1)) (locate (finProdFinEquiv.symm (finProdFinEquiv (v,offset k j))).1 slot.1 slot.2))=_
  rw [Equiv.symm_apply_apply,atSlot]
  change readAt (E.symm (E z))=readAt z
  rw [E.symm_apply_apply z]

def mounted (books : Fin S→Raw) (shelves : Fin S→Rows) := ∀i,∀v : Fin (books i).1.val,∀k : K,∀j : Fin (len k),
  wordBits _ (shelves i (group k)) (locate (v.castLE (Nat.le_of_lt_succ (books i).1.isLt)) k j)=
    (value ((books i).2 v) k).val.testBit j.val

theorem source (books : Fin S→Raw) (shelves : Fin S→Rows) (fit : V*width≤B) (bp : 0<B)
    (rows : mounted books shelves) (i : Fin S) :
    Source (books i) (i.val*B) (bitsAt (fun k=>weave (shelves k) fit) bp) := by
  intro v k j
  let v0:=v.castLE (Nat.le_of_lt_succ (books i).1.isLt)
  let b:=finProdFinEquiv (v0,offset k j)
  have ordinal : b.val=v.val*width+(offset k j).val := by
    change (offset k j).val+width*v.val=_
    ring
  let page (s : Fin S) := weave (shelves s) fit
  have atPage := congrArg (fun x : Word B=>wordBits B x (b.castLE fit)) (dense_page page bp i.val)
  have read : bitsAt page bp (i.val*B+b.val)=wordBits B (page i) (b.castLE fit) := by
    simpa only [DescentTerminalDenseWindow.dense,Equiv.apply_symm_apply,Fin.val_castLE,
      aligned,i.isLt,dite_eq_left,Fin.eta] using atPage
  change bitsAt page bp (i.val*B+(v.val*width+(offset k j).val))=_
  rw [←ordinal]
  exact read.trans ((weave_read (shelves i) fit v0 k j).trans (rows i v k j))

end
end Hierarchy.DescentTerminalVertexFields

end OAI
