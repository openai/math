import OAI.Hierarchy.DescentPhysicalResetTrunkScene
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # The same compact relay row remains available to the later source-ticket reader -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentResetTrunkCompactPointer DescentSIMDLookup DescentPackedZip DescentDyadicSpan ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false
variable (v : CandidateFront) (floor : ℕ) (s : v.Scene) {w P N : ℕ} (safe : v.SceneRoom floor s w)
local notation "base₀" => v.mixed floor
local notation "latch₀" => v.gathered floor
local notation "n₀" => v.newHosts*chunks v.peer.groups v.peer.lanes
local notation "rows₀" => DescentResetTrunkCompactGather.rows base₀ v.newHosts v.peer.groups v.peer.lanes
local notation "Row₀" => Row v.newHosts v.peer.groups v.peer.lanes
local notation "pos₀" => row v.newHosts v.peer.groups v.peer.lanes
local notation "banks₀" => v.trunkBanks floor s
local notation "entry₀" m => (v.received floor s safe).image m
local notation "last₀" m => (v.trunkScene floor s safe).image m

theorem trunk_sibling_word (m : Memory w) (pitch : P=v.peer.hosts)
    (name : Fin N→Fin P) (other : Fin N→Option (Fin N)) (live : N≤v.newHosts)
    (active : N≤ s.inverse.size) (census : Measured banks₀ name other (entry₀ m))
    (room : v.trunkEnd floor<2^w) (p : Row₀) :
    (last₀ m) (rows₀+(pos₀ p).val)=
      ((pointer live other p.1).elim n₀ (fun t=>(pos₀ (t,p.2)).val):Word w):=by
  subst P
  let board:=DescentResetTrunkCompactGather.phase w base₀ v.newHosts v.peer.hosts v.peer.groups v.peer.lanes banks₀
  have high : latch₀≤v.trunkEnd floor:=Nat.le_add_right ..
  have got:=DescentResetTrunkCompactGather.publish (b:=1) (G:=v.peer.groups) (M:=v.peer.lanes) base₀ banks₀
    name other live (entry₀ m) (v.trunk_room floor s safe active) census (high.trans_lt room)
  have earlier : rows₀+(pos₀ p).val<latch₀:=
    Nat.add_lt_add_left ((pos₀ p).isLt.trans_le (span_ge n₀)) _
  have keep:=DescentOrdinaryAtomFieldRAM.ROM.frame (DescentResetTrunkIssue.pages v.metaBits v.peer.lanes)
    (DescentResetTrunkIssue.width v.metaBits v.peer.lanes) latch₀ (board.image (entry₀ m)) _ (.inl earlier)
  apply keep.trans
  simpa only [Nat.cast_mul] using got.2.2.1 p

/-- A later source-ticket bank is read at the receiver's actual compact relay.
This uses a single previously published pointer for all ticket bits. -/
theorem trunk_sibling_read {b : ℕ} (m current : Memory w) (pitch : P=v.peer.hosts)
    (name : Fin N→Fin P) (other : Fin N→Option (Fin N)) (live : N≤v.newHosts)
    (active : N≤ s.inverse.size) (census : Measured banks₀ name other (entry₀ m))
    (room : v.trunkEnd floor<2^w) (endAt : ℕ) (endWord : endAt<2^w) (early : latch₀≤endAt)
    (cols : Bank) (val : Fin v.newHosts→Fin v.peer.groups→Cell b)
    (fits : cols.Fits w endAt) (size : n₀≤cols.size) (reads : DescentPackedColony.Reads cols val v.peer.lanes current)
    (kept : ∀p : Row₀,current (rows₀+(pos₀ p).val)=(last₀ m) (rows₀+(pos₀ p).val)) :
    (DescentResetTrunkGather.issue n₀ rows₀ cols).Fits w endAt ∧
      Source (DescentResetTrunkGather.issue n₀ rows₀ cols)
        (fun h g=>(pointer live other h).elim 0 (fun t=>val t g)) v.peer.lanes current:=
  DescentResetTrunkCompactGather.late_source base₀ endAt (pointer live other) cols val (last₀ m) current
    endWord early fits size reads (v.trunk_sibling_word floor s safe m pitch name other live active census room) kept

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
