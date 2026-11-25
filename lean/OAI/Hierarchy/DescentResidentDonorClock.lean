import OAI.Hierarchy.DescentResidentDonorFields
import OAI.Hierarchy.DescentDonorLayoutBit
import OAI.Hierarchy.DescentPrivateDepotClock

namespace OAI
/-! # The six actual native expressions in one ordinary donor event -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Resident
open DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentPackedZip DescentPackedColony
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) {H G M K : ℕ}
local notation "count" => DescentPacking.PackedMatch.Local.«fields» s.blocks s.degree (2*s.cap)

/-- Published signed words and painted winner records use the preceding
date's stable addresses. Both terrain and owner resolvers reuse that same
panel and the one globally compared layout bit. -/
structure Addressed (s : DepotRAM.Shape) (K : ℕ) where
  layout : Owners.LayoutBit.Banks
  winner : Fin s.blocks→Bank
  marked : Fin s.blocks→Fin (2*s.cap)→Bank
  cable : Fin (s.blocks*(2*s.cap))→Bank
  venues : Fin (DescentPacking.PackedMatch.Local.«fields» s.blocks s.degree (2*s.cap))→Tables
  source : Sources s K

def addressed (B : Addressed s K) (H : ℕ) : Sources s K :=
  { B.source with
    terrain:=Owners.LayoutBit.field B.layout (Gather.assembly B.venues (Gather.expr B.winner B.marked B.source.peers H))
    signed:=fun i=>.lookup (B.cable i) .row }

def terrainLimit (r D cap : ℕ) := 31 + (r+(r*(2*cap)+D*r))*56
def fieldLimit (r D cap K : ℕ) :=
  let u:=terrainLimit r D cap
  u+(1+r*(2*cap)*18)+(1+(D+1)*75)+(1+40*(D+1)^4)+(1+40*(D+1)^4)+(1+K*(u+50))

theorem assembled_work {r D cap : ℕ} (Q : Owners.LayoutBit.Banks)
    (win : Fin r→Bank) (marked : Fin r→Fin (2*cap)→Bank) (ports : Ports D) (H : ℕ)
    (tables : Fin (DescentPacking.PackedMatch.Local.«fields» r D (2*cap))→Tables) :
    (Owners.LayoutBit.field Q (Gather.assembly tables (Gather.expr win marked ports H))).work≤terrainLimit r D cap := by
  let fields_:=Gather.expr win marked ports H
  have size (i : Fin (DescentPacking.PackedMatch.Local.«fields» r D (2*cap))) : (fields_ i).work≤45 := by
    induction i using Fin.addCases with
    | left j => simp [fields_,Gather.expr,Fin.addCases_left,Expr.work]
    | right j => induction j using Fin.addCases <;> simp only [fields_,Gather.expr,Fin.addCases_right,Fin.addCases_left] <;> simp [peerExpr,neighborID,Expr.work]
  have assembled:=Gather.collect_work tables fields_ (List.finRange (DescentPacking.PackedMatch.Local.«fields» r D (2*cap))) 45 size
  have final:=Owners.LayoutBit.work Q (Gather.assembly tables fields_)
  simp only [List.length_finRange] at assembled
  exact final.trans (by unfold Gather.assembly;unfold terrainLimit DescentPacking.PackedMatch.Local.«fields» at *;omega)

theorem terrain_work (B : Addressed s K) (H : ℕ) :
    (addressed s B H).terrain.work≤terrainLimit s.blocks s.degree s.cap := by
  exact assembled_work B.layout B.winner B.marked B.source.peers H B.venues

theorem field_work (B : Addressed s K) (H G M : ℕ) :
    fieldWork («fields» s z (addressed s B H) H G M)≤fieldLimit s.blocks s.degree s.cap K := by
  let R:=addressed s B H
  have raw:=terrain_work s B H
  have signed_:=Gather.collect_work R.cableTables R.signed (List.finRange (s.blocks*(2*s.cap))) 7 (fun _=>by simp [R,addressed,Expr.work])
  have owned:=Owners.clock R.ownerTables R.peers R.owner H
  have ranks:=DescentHaloPackedRebase.context_work R.ranks
  have hubs:=DescentHaloPackedRebase.context_work R.hubs
  have fee:=Fresh.work R.fresh R.terrain H G M (SixBirths.width z M)
  have product:=Nat.mul_le_mul_left K (Nat.add_le_add_right (terrain_work s B H) 50)
  simp only [List.length_finRange] at signed_
  change R.terrain.work≤terrainLimit s.blocks s.degree s.cap at raw
  unfold fieldWork «fields» fieldLimit
  simpa only [Gather.assembly,Owners.aggregate,DescentHaloWalkRAM.breadth] using
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add raw signed_) owned) ranks) hubs)
      (fee.trans (Nat.add_le_add_left product 1))

/-- All spatial, history and age factors may be charged to one public
integer bound. The fourth power accounts for four neighbor steps. -/
theorem field_limit_quartic {r D cap K N : ℕ} (nr : r≤N) (nd : D+1≤N) (nc : cap≤N) (nk : K≤N) :
    fieldLimit r D cap K ≤ 800*N^4 := by
  have one : 1≤N:=by omega
  have dn : D≤N:=by omega
  have rc : r*cap≤N*N:=Nat.mul_le_mul nr nc
  have dr : D*r≤N*N:=Nat.mul_le_mul dn nr
  have pow2 : N≤N*N := by simpa using Nat.mul_le_mul_right N one
  have p2 : N*N≤N^4:=by calc
    N*N = N^2:=by ring
    _ ≤ N^4:=Nat.pow_le_pow_right one (by decide)
  have p3 : N*(N*N)≤N^4:=by calc
    N*(N*N)=N^3:=by ring
    _ ≤ N^4:=Nat.pow_le_pow_right one (by decide)
  have du : (D+1)^4≤N^4:=Nat.pow_le_pow_left nd 4
  have u : terrainLimit r D cap≤255*(N*N) := by
    unfold terrainLimit
    rw [show r*(2*cap)=2*(r*cap) by ring];omega
  have wider : terrainLimit r D cap+50≤305*(N*N):=by omega
  have billed := Nat.mul_le_mul nk wider
  rw [show N*(305*(N*N))=305*(N*(N*N)) by ring] at billed
  unfold fieldLimit
  dsimp only
  rw [show r*(2*cap)=2*(r*cap) by ring]
  omega

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Resident

end OAI
