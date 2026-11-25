import OAI.Hierarchy.TaggedWireTurnStartRead
import OAI.Hierarchy.TaggedWireReportOrder
import OAI.Hierarchy.ProtocolRAMTurnAuthenticated
import OAI.Hierarchy.ProtocolRAMTurnStepOrder
import OAI.Hierarchy.TaggedWireNativeRoleSides

namespace OAI
/-! # The weighted earlier rank of the real paid terminal occurrence -/

noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
namespace Hierarchy.WireTelescope.SettledMatrix.Layout
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor AdaptiveProbe
open TaggedShorterCommonScan ProtocolRAM ProbeStage.CoreBoard.HistoryRoles
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
variable {K edges extra W : ℕ} {I C : Type} [Fintype I] [Fintype C]
    (L : SettledMatrix.Layout K edges I C) (enum : Fin extra≃RouteOccurrence L.core L.center)
    (fixed : Fin edges→ℕ) (stock : I→ℕ) (reserved used : C→ℕ)
local notation "ind" => L.nativeOrder enum
local notation "mass" => bits fixed stock reserved used
local notation "key" => L.nativeEdge enum
local notation "loads" => L.nativeWidth enum fixed stock reserved used
local notation "In" => Fin (Fintype.card (Source edges I C))

/-- At the original (uncompressed) source-hop ordinal, NativeSlot.start is the
weighted earlier value of the paid CPU's actual edge and amount columns. -/
theorem start_eq_printed (i : In) (j : Fin (L.routes i).length) :
    NativeSlot.start L.routes mass ind i j=earlier key loads ((L.nativeOrder enum).symm ⟨i,j⟩).val (key ((L.nativeOrder enum).symm ⟨i,j⟩)) := by
  have which : NativeSlot.edge L.routes ind=key := funext (L.native_edge enum)
  have how : NativeSlot.amount (route:=L.routes) (bits:=mass) (rows:=ind)=loads :=
    funext (L.native_width enum fixed stock reserved used)
  unfold NativeSlot.start
  rw [which,how]

/-- The decoded pointer is from the fourth word of the native rank row, using
the same width/slot ordinal as the original native itinerary. -/
theorem start_ram (b : RoleProgram.Board) (keys : Bank) (rankBase bits : ℕ) (m : Memory W)
    (wordRoom : 4*(edges+extra)≤2^W) (bankRoom : 4*(edges+extra)≤2^bits)
    (stored : ∀t : Fin (edges+extra),m (rankBase+4*t.val+3)=(earlier key loads t.val (key t):Word W))
    (i : In) (j : Fin (L.routes i).length) (positive : 0< mass i)
    (small : routeLoad L.routes mass ((L.routes i).get j)<2^W) :
    (ProtocolRAMTurnSnapshot.values (b.itinerary keys ⟨rankBase+3,bits⟩) m).starts ((L.nativeOrder enum).symm ⟨i,j⟩).val =
      NativeSlot.start L.routes mass ind i j := by
  have enough := (NativeSlot.start_room L.routes mass ind i j positive).trans_lt small
  have fit : NativeSlot.start L.routes mass ind i j<2^W := by omega
  apply ProtocolRAMTurnSnapshot.rank_at b keys rankBase bits ((L.nativeOrder enum).symm ⟨i,j⟩) _ m wordRoom bankRoom fit
  rw [L.start_eq_printed enum fixed stock reserved used i j]
  exact stored _


end Hierarchy.WireTelescope.SettledMatrix.Layout

namespace Hierarchy.ProtocolRAMTurnStepOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix ProtocolRAMTurnItinerary
open ProtocolRAM.Calendar CoreRoute HistoryRoles RoleProgram
open scoped Classical

variable {h d k K W : ℕ} (S : PurchaseSampler) (board : RoleProgram.Board)
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place board.edges) (inj : Function.Injective place)
    (pad : Chord K) (o : Orders h d k)
local notation "L" => B.matrixLayout inj pad
local notation "occ" => board.edges+Fintype.card (Slots h d k)
local notation "sources" => SettledMatrix.Source board.edges (Commodity (Fin (2^h)) (Stages h d) k) (Columns h d×Fin k)
local notation "num" => Layout.numbered (r:=board.edges) (I:=Commodity (Fin (2^h)) (Stages h d) k) (A:=Columns h d×Fin k)
local notation "index" => (L).nativeOrder (enum B o)

theorem original_address (i : Fin (Fintype.card sources)) (q : Fin ((L).routes i).length) :
    address B inj pad o (num i) q=(index).symm ⟨i,q⟩ := by
  apply (index).injective
  rw [Equiv.apply_symm_apply]
  refine (actual_order B inj pad o (num i) q).trans ?_
  exact (Equiv.symm_apply_eq _).mpr rfl

/-- Both real rank-tape values used by the paid turn, on the original
matrix source and at its actual reported walk boundary. -/
theorem live_starts (fixed : Fin board.edges→ℕ) (stock : Commodity (Fin (2^h)) (Stages h d) k→ℕ)
    (reserved used : Columns h d×Fin k→ℕ) (keys : Bank) (rankBase bits : ℕ) (m : Memory W)
    (wordRoom : 4*occ≤2^W) (bankRoom : 4*occ≤2^bits)
    (i : Fin (Fintype.card sources)) (posWidth : 0<Layout.bits fixed stock reserved used i)
    (margins : ∀q : Fin ((L).routes i).length,routeLoad (L).routes
      (Layout.bits fixed stock reserved used) (((L).routes i).get q)<2^W)
    (stored : ∀t : Fin occ,m (rankBase+4*t.val+3)=(TaggedShorterCommonScan.earlier
      ((L).nativeEdge (enum B o)) ((L).nativeWidth (enum B o) fixed stock reserved used)
      t.val ((L).nativeEdge (enum B o) t):Word W))
    (sp : Spine (rowGraph (L).edge) ((L).family i).1.1 ((L).routes i) ((L).family i).1.2)
    (j : Fin (((L).routes i).length+1)) (t : Turn)
    (orig : t.origin=ProtocolRAMTurnGeometry.origin o (num i))
    (len : t.length=ProtocolRAMTurnGeometry.length (num i))
    (rev : t.reverse=reverse B inj pad (num i)) (pos : t.position=j.val) :
    let v:=ProtocolRAMTurnSnapshot.values (board.itinerary keys ⟨rankBase+3,bits⟩) m
    let z:=sp.sides (.inl false) (.inl true) 0 j
    t.start v false=refStart (L).routes (Layout.bits fixed stock reserved used) index i z.1 ∧
    t.start v true=refStart (L).routes (Layout.bits fixed stock reserved used) index i z.2 := by
  intro v z
  have actualLen:=len.trans (step_count S board B inj pad (num i)).symm
  apply start_sides (L).family (L).edge (L).routes _ index i sp j t v actualLen pos
    (fun q=>(address B inj pad o (num i) q).val)
  · intro q hq
    rw [previous t q.val (by rw [pos,←hq]; rfl) (q.isLt.trans_le actualLen.ge),orig,len,rev]
    exact (address_val B inj pad o (num i) q).symm
  · intro q hq
    rw [next t q.val (by rw [pos,←hq]; rfl) (q.isLt.trans_le actualLen.ge),orig,len,rev]
    exact (address_val B inj pad o (num i) q).symm
  · intro q
    exact (congrArg v.starts (congrArg Fin.val (original_address S board B inj pad o i q))).trans <|
      (L).start_ram (enum B o) fixed stock reserved used board keys rankBase bits m wordRoom bankRoom
      stored i q posWidth (margins q)


end Hierarchy.ProtocolRAMTurnStepOrder

end
end OAI
