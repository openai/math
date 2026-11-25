import OAI.Hierarchy.DescentDatedSignedLocalRecords
import OAI.Hierarchy.DescentSignedBankRoom
import Mathlib.Order.Fin.Basic

namespace OAI
/-! The successive actual addresses of the signed date, and containment of
the three packed rank layouts before their first possible use. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s:SignedExtent) (base:ℕ)

def cuts:Fin 22→ℕ:=![base,s.mapBase base,s.viewBase base,s.keyStart base,s.lookupStart base,
  s.ranksStart base,s.peerStart base,s.localStart base,s.projectedStart base,s.forwardBase base,
  s.backBase base,s.routeStart base,s.returnedStart base,s.shapesStart base,s.rawStart base,
  s.metaStart base,s.gateStart base,s.peerKeyBase base,s.peerROMBase base,s.peerHeadBase base,
  s.peerHeadOut base,s.tailStart base]

theorem cuts_mono:Monotone (s.cuts base):=by
  apply Fin.monotone_iff_le_succ.2
  intro j
  fin_cases j <;> exact Nat.le_add_right _ _

theorem clock_room {w:ℕ} (room:s.roof base+max s.slab s.oldSlab<2^w):
    ∀j:Fin 22,s.cuts base j+max s.slab s.oldSlab<2^w:=by
  intro j
  have order : s.tailStart base ≤ s.roof base := (s.prefix_room base).trans_eq (s.calibrated base)
  have lower:s.cuts base j ≤ s.tailStart base:=s.cuts_mono base (show j≤(21:Fin 22) by omega)
  exact (Nat.add_le_add_right (lower.trans order) _).trans_lt room

local notation "PathTable"=>DescentOrdinaryDonorSources.PathKeys.table (s.keyStart base) s.degree s.fieldBits s.fieldBits s.lanes
local notation "PTable"=>DescentOrdinaryDonorSources.ROM.table (s.peerStart base) s.lowSites s.fieldBits s.lanes
variable {w:ℕ} (I:s.Input)
theorem key_room (z:s.Socket) (i:Fin 5) (last:Fin 22) (issued:(4:Fin 22)≤last)
    (x:(I.path z).Fits w base) (y:∀t,(I.endpoints z t).Fits w base) (space:s.cuts base last<2^w):
    DescentPackedZip.Fits PathTable (I.path z) (I.endpoints z (DescentOrdinaryDonorSources.PathKeys.side i))
      s.fieldBits s.fieldBits s.lanes (s.cuts base last) w:=by
  have early:base ≤ s.cuts base last:=s.cuts_mono base (Fin.zero_le last)
  have sep:s.lookupStart base ≤ s.cuts base last:=s.cuts_mono base issued
  apply binary_fits _ _ _ _ _ (ProtocolRAMGeneratedWrite.fits_mono _ early x)
    (ProtocolRAMGeneratedWrite.fits_mono _ early (y _)) (fun _=>rfl) _ le_rfl sep space
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

theorem rank_room (z:s.Socket) (i:Fin 5) (last:Fin 22) (issued:(5:Fin 22)≤last)
    (x:(I.path z).Fits w base) (y:∀t,(I.endpoints z t).Fits w base) (space:s.cuts base last+s.slab<2^w):
    DescentPackedChildNeighbor.SIMD.Room (DescentPackedChildNeighbor.SIMD.ROM.layout (s.lookupStart base)
      (s.reach*s.reach) s.fieldBits s.fieldBits s.lanes (Nat.clog 2 s.slab)
      (subbank (s.viewBase base) s.viewRows (fieldNumber (DescentOrdinaryDonorSources.tag i))))
      ((PathTable).read (I.path z) (I.endpoints z (DescentOrdinaryDonorSources.PathKeys.side i)))
      s.hosts s.groups s.fieldBits s.fieldBits s.lanes w (s.cuts base last):=by
  have wide:s.cuts base last<2^w:=(Nat.le_add_right ..).trans_lt space
  have key:=s.key_room base I z i last ((by decide : (4:Fin 22)≤5).trans issued) x y wide
  have field (f:DescentOrdinaryDonorRankDirectory.Field):fieldNumber f<3:=by cases f <;> decide
  apply packed_room
  · apply slice_fits (⟨_,field _⟩:Fin 3)
    · exact s.cuts_mono base ((by decide : (3:Fin 22)≤5).trans issued)
    · exact wide
  · exact span_ge _
  · exact ⟨key.apply,key.right,key.shift,key.left⟩
  · have paid:s.ranksStart base ≤ s.cuts base last:=s.cuts_mono base issued
    simpa only [ranksStart,lookupWords,slab,Nat.add_assoc] using paid
  · exact space

theorem donor_room (z:s.Socket) (i:Fin 5) (j:Fin 6) (last:Fin 22) (issued:(7:Fin 22)≤last)
    (old:(I.donor z j).Fits w base) (space:s.cuts base last<2^w):
    DescentPackedZip.Fits PTable (.lookup (s.rankPage base z i) .row) (I.donor z j)
      s.fieldBits s.fieldBits s.lanes (s.cuts base last) w:=by
  have lo:s.peerStart base ≤ s.cuts base last:=s.cuts_mono base ((by decide:(6:Fin 22)≤7).trans issued)
  have bank:=(slice_fits (finProdFinEquiv (s.socketId z,i)) lo space)
  have hi:base ≤ s.cuts base last:=s.cuts_mono base (Fin.zero_le last)
  have loaded : (Expr.lookup (s.rankPage base z i) .row).Fits w (s.cuts base last) := ⟨bank,trivial⟩
  apply binary_fits _ _ _ _ _ loaded (ProtocolRAMGeneratedWrite.fits_mono _ hi old) (fun _=>rfl)
    _ le_rfl (s.cuts_mono base issued) space
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

theorem local_room (room:s.roof base+max s.slab s.oldSlab<2^w)
    (path:∀z,(I.path z).Fits w base) (ends:∀z t,(I.endpoints z t).Fits w base)
    (old:∀z j,(I.donor z j).Fits w base):s.LocalRoom I base w:=by
  have wide:=s.clock_room base room 21
  have rows:s.cuts base 21+s.slab<2^w:=(Nat.add_le_add_left (le_max_left ..) _).trans_lt wide
  have early:s.cuts base 21<2^w:=(Nat.le_add_right ..).trans_lt rows
  have padded:span s.slab ≤ s.cuts base 21:=by
    have lhs:span s.slab ≤ s.mapIndices:=by unfold mapIndices;omega
    have middle:s.mapIndices ≤ s.viewBase base:=by unfold viewBase mapWords;omega
    exact (lhs.trans middle).trans (s.cuts_mono base (by decide:(2:Fin 22)≤21))
  exact ⟨fun z i=>s.key_room base I z i 21 (by decide) (path _) (ends _) early,
    fun z i=>s.rank_room base I z i 21 (by decide) (path _) (ends _) rows,
    fun z i j=>s.donor_room base I z i j 21 (by decide) (old _ _) early,padded.trans_lt early⟩

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
