import OAI.Hierarchy.DescentTerminalPackedPopulation
import OAI.Hierarchy.DescentTerminalMaskPage

namespace OAI
/-! # Terminal resident books at arbitrary occupied group/block slots of one host -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentPackedLocalAtoms
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {q t H N A w V C S B : ℕ}
local notation "width" => span q t H N A w
local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)
local notation "Rows" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V
local notation "Venue" => (f : Fin 8)→Word (sized f)

theorem densified_bit (mask : Fin C→Word 1) (cells : Fin C→Venue) (u : Fin C) (v : Fin V)
    (alive : mask u≠0) (rank : earlier mask u=v.val) (f : Fin 8) (j : Fin (sized f)) :
    wordBits _ (densified mask cells f) (finProdFinEquiv (v,j))=wordBits _ (cells u f) j := by
  simp [densified,field_at mask (fun c=>cells c f) u alive v rank]

theorem at_resident (mask : Fin C→Word 1) (cells : Fin C→Venue) (u : Fin C) (v : Fin V)
    (alive : mask u≠0) (rank : earlier mask u=v.val) (k : Key H N A) :
    raw (densified mask cells) v k=venueField (cells u) k := by
  unfold raw venueField
  congr 2
  funext j
  exact densified_bit mask cells u v alive rank _ _

theorem masked_source (books : Fin S→Raw) (mask : Fin S→Fin C→Word 1) (cells : Fin S→Fin C→Venue)
    (whereAt : (i : Fin S)→Fin (books i).1.val→Fin C)
    (alive : ∀i v,mask i (whereAt i v)≠0) (rank : ∀i v,earlier (mask i) (whereAt i v)=v.val)
    (fit : V*width≤B) (bp : 0<B) (zero : ∀i v,Zeros ((books i).2 v))
    (source : ∀i v k,allows (fun a=>(value ((books i).2 v) a).val) k→venueField (cells i (whereAt i v)) k=(value ((books i).2 v) k).val)
    (i : Fin S) :
    Source (books i) (i.val*B) (bitsAt (fun a=>clippedPage (densified (mask a) (cells a)) fit) bp) := by
  apply clipped_source books (fun a=>densified (mask a) (cells a)) fit bp zero _ i
  intro home v k h
  exact (at_resident (mask home) (cells home) (whereAt home v)
    (v.castLE (Nat.le_of_lt_succ (books home).1.isLt)) (alive home v) (rank home v) k).trans
    (source home v k h)

end
end Hierarchy.DescentTerminalVertexFields

end OAI
