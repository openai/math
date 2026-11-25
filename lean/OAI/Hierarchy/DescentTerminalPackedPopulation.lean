import OAI.Hierarchy.DescentTerminalCellCoordinates
import OAI.Hierarchy.DescentTerminalSiblingFrames

namespace OAI
/-! # Recovering the exact little-endian field in the reached dense venue population -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalDenseWindow
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {q t H N A w M V S B bits : ℕ}
local notation "width" => span q t H N A w
local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
local notation "Group" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) M
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)
local notation "Venue" => (f : Fin 8)→Word (sized f)

def groupsOf (venue : ℕ→Venue) (k : ℕ) : Group := fun f=>
  (wordBits _).symm fun j=>
    let dst : Fin M×Fin (sized f):=finProdFinEquiv.symm j
    wordBits _ (venue (k*M+dst.1.val) f) dst.2

theorem group_digit (venue : ℕ→Venue) (mp : 0<M) (n : ℕ) (f : Fin 8) (j : Fin (sized f)) :
    streamBit (groupsOf venue) mp n f j=wordBits _ (venue n f) j := by
  simp [streamBit,groupsOf,Nat.mul_comm (n/M) M,Nat.div_add_mod]

theorem group_field (venue : ℕ→Venue) (mp : 0<M) (n : ℕ) (k : Key H N A) :
    groupField (groupsOf venue) mp n k=venueField (venue n) k := by simp [groupField,venueField,group_digit]

/-- The two final readable sentinels cover trailing positions of population zero,
including an exactly full final batch. They carry no contribution to a live vertex. -/
def sourceWords (books : Fin S→Raw) (M : ℕ) := population books S/M+2

theorem access_room (books : Fin S→Raw) (M : ℕ) (i : Fin S) (d : Fin 2) :
    population books i.val/M+d.val<sourceWords books M := by
  have upto : population books i.val≤population books S := pref_mono _ i.isLt.le
  have half:=Nat.div_le_div_right (c:=M) upto
  unfold sourceWords
  have:=d.isLt;omega

theorem source_budget (books : Fin S→Raw) (mp : 0<M) (wide : V≤M) : sourceWords books M≤S+2 := by
  have total : population books S≤S*M := by
    simpa [population,pref] using delta (fun i:Fin S=>(books i).1.val)
      (fun i=>(Nat.le_of_lt_succ (books i).1.isLt).trans wide) 0 S
  have quot:=Nat.div_le_div_right (c:=M) total
  simpa [sourceWords,Nat.mul_div_cancel _ mp] using Nat.add_le_add_right quot 2

theorem columns_from_store (L : PackedShelf) (books : Fin S→Raw) (venue : ℕ→Venue) (m : Memory bits)
    (written : ∀k:Fin (sourceWords books M),∀f,(L.columns f).read m (k.val:Word bits)=((groupsOf (M:=M) venue k.val f).val:Word bits))
    (i : Fin S) (d : Fin 2) (f : Fin 8) :
    (L.columns f).read m ((population books i.val/M+d.val:ℕ):Word bits)=
      ((groupsOf (M:=M) venue (population books i.val/M+d.val) f).val:Word bits) :=
  written ⟨_,access_room books M i d⟩ f

theorem position_source (books : Fin S→Raw) (venue : ℕ→Venue) (wide : V≤M) (mp : 0<M) (fit : V*width≤B)
    (bp : 0<B) (zero : ∀i v,Zeros ((books i).2 v))
    (read : ∀i (v : Fin (books i).1.val) k,allows (fun a=>(value ((books i).2 v) a).val) k→
      venueField (venue (population books i.val+v.val)) k=(value ((books i).2 v) k).val) (i : Fin S) :
    Source (books i) (i.val*B) (bitsAt (fun a=>clippedPage (siblings books wide mp (groupsOf venue) a) fit) bp) := by
  apply siblings_source books (groupsOf venue) wide mp fit bp zero _ i
  intro a v k hk
  rw [group_field]
  exact read a v k hk

end
end Hierarchy.DescentTerminalVertexFields

end OAI
