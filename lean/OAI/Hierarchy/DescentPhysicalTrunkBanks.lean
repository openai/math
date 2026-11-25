import OAI.Hierarchy.DescentPhysicalTrunkHeader
import OAI.Hierarchy.DescentResetTrunkCompactProgram

namespace OAI
/-! # The compact trunk uses the count, prefix and inverse from the reached actor census -/
namespace Hierarchy.DescentResetTrunkCompactPointer
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
theorem Measured.at_bases {N P w : ℕ} {B C : Banks} {name : Fin N→Fin P} {peer : Fin N→Option (Fin N)}
    {m : Memory w} (input : Measured B name peer m) (here : C.here.base=B.here.base)
    (turn : C.turn.base=B.turn.base) (number : C.number.base=B.number.base) (total : C.total.base=B.total.base) :
    Measured C name peer m:=by
  exact ⟨by simpa only [total] using input.count,fun i=>by simpa only [here] using input.here i,
    fun i=>by simpa only [turn] using input.turn i,fun i=>by simpa only [number] using input.number i⟩
end Hierarchy.DescentResetTrunkCompactPointer

namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentDyadicSpan DescentSIMDLookup DescentSixParty.Chronology ProtocolRAM DescentResetTrunkCompactPointer
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (floor : ℕ) (s : v.Scene)
local notation "peer₀" => v.peer
local notation "P₀" => (peer₀).hosts
local notation "date₀" => v.peers floor
local notation "pal₀" => (peer₀).threshold date₀
local notation "scalar₀" => (peer₀).endAddress date₀

def trunkBanks : DescentResetTrunkCompactPointer.Banks where
  here:=s.inverse
  turn:=DescentSixParty.ClosedReset.Window.scalarBank pal₀ P₀ 1
  number:=⟨s.count.base-P₀,Nat.clog 2 P₀⟩
  total:=s.count

/-- After the completed parent-directory pass the entire dyadic prefix bank,
including unused suffix addresses, lies below the start of the trunk scatter. -/
theorem trunk_room {w N : ℕ} (safe : v.SceneRoom floor s w) (active : N≤ s.inverse.size) :
    Room (v.trunkBanks floor s) N v.newHosts P₀ w (v.mixed floor):=by
  let stop:=v.mixed floor
  have runway : scalar₀+span P₀≤v.parentEnd floor:=by
    change scalar₀+span P₀≤DescentResetParentAperture.endAddress (scalar₀+v.newHosts) P₀ v.newHosts
    rw [DescentResetParentAperture.extent];omega
  have last:=(v.front_order floor).2.1
  have early : scalar₀≤ stop:=((Nat.le_add_right ..).trans runway).trans last
  have word:=safe.stems.final
  have up (k : Bank) (small : k.Fits w scalar₀) : k.Fits w stop:=⟨small.1,small.2.1,small.2.2.trans early⟩
  have end₀ : pal₀+2*P₀+span P₀≤ scalar₀:=le_rfl
  have right:=DescentSixParty.ClosedReset.Window.scalar_bank_room end₀ safe.peers.total (1:Fin 3)
  have start : s.count.base≤ scalar₀:=(Nat.le_add_right ..).trans safe.count.2.2
  have rankEnd : s.count.base-P₀+span P₀≤ stop:=
    (Nat.add_le_add_right ((Nat.sub_le ..).trans start) _).trans (runway.trans last)
  have spanFit : span P₀<2^w:=(Nat.le_add_left ..).trans_lt (rankEnd.trans_lt word)
  have hostsFit : v.newHosts<2^w:=(Nat.le_add_left ..).trans_lt safe.parent
  exact ⟨up _ safe.inverse,up _ right,⟨span_pos _,spanFit,rankEnd⟩,up _ safe.count,active,
    span_ge _,span_ge _,hostsFit,(span_ge _).trans_lt spanFit⟩

/-- The clocks and output transforms on arbitrary RAM never inspect a
cardinality witness for live actors. The measured census uses the same code. -/
theorem trunk_any {w : ℕ} (safe : v.SceneRoom floor s w) (m : Memory w) (room : v.trunkEnd floor<2^w) :
    let p:=DescentResetTrunkCompactProgram.phase w (v.mixed floor) v.newHosts P₀ (peer₀).groups
      (peer₀).lanes v.metaBits (v.trunkBanks floor s)
    p.Runs m ∧ ∀a,a<v.mixed floor ∨ v.trunkEnd floor≤a →p.image m a=m a:=
  DescentResetTrunkCompactProgram.any (v.mixed floor) _ m (v.trunk_room floor s safe (Nat.zero_le _)) room

/-- When the count word follows a real raw prefix, the bound field in
the compact program is its genuine source base. -/
theorem trunk_prefix_base (start : ℕ) (counted : s.count.base=start+P₀) :
    (v.trunkBanks floor s).number.base=start:=by
  change s.count.base-P₀=start
  rw [counted,Nat.add_sub_cancel]

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
