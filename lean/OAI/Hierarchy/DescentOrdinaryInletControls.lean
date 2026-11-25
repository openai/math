import OAI.Hierarchy.DescentOrdinaryInletChip
import OAI.Hierarchy.DescentOrdinaryRoleControlRead

namespace OAI
/-! # The actual population and local venue controls for the ordinary gather -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentPackedColony DescentPackedZip DescentOrdinaryAtomFieldRAM DescentSIMDLookup DescentSharedCableNames
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)
variable (floor : ℕ) {w : ℕ} (m : Memory w)
local notation "H₀" => A.clip.venue.hosts
local notation "G₀" => A.clip.venue.groups
local notation "M₀" => A.clip.working
local notation "L₀" => A.population v floor
local notation "P₀" => A.ports v floor
local notation "field₀" => A.clip.fieldBank (v.signedEnd floor)
local notation "dst₀" => (A.inlet v floor w).image m

theorem clipped_before_count (safe : A.Room v floor w) :
    ∀i,i<A.priorStart v floor → A.chipTape v floor m i=A.clippedTape v floor m i :=by
  obtain ⟨_,old,role,_,_⟩:=A.inlet_order v floor
  let frames:=A.inlet_frames v floor m safe
  intro i lo
  exact (frames.chip i (lo.trans_le (old.trans role))).trans ((frames.role i (lo.trans_le old)).trans (frames.old i lo))

theorem inlet_controls (safe : A.Room v floor w) (order : Fin H₀→Fin (L₀).walks→Option (Fin H₀))
    (roles : Fin A.previous.blocks→Fin A.previous.hosts→Fin G₀→Cell ((L₀).roleBits*(L₀).nodes)) (someBlock : Fin A.previous.blocks)
    (positive : 0<A.rolePitch)
    (early : ∀x,(A.role x).base+(A.role x).size≤v.signedEnd floor)
    (capacity : ∀x,A.previous.hosts*chunks G₀ A.rolePitch≤(A.role x).size)
    (before : ∀x,Reads (A.role x) (roles x) A.rolePitch m)
    (mounted : Mounted P₀ (DescentSortedRoster.indexed order) (A.clippedTape v floor m) G₀ M₀)
    (ports : ∀bank : Bank,bank.Fits w (A.priorStart v floor)→H₀*chunks G₀ M₀≤bank.size→
      Accessible P₀ bank H₀ G₀ M₀ w (A.priorStart v floor)) :
    Mounted P₀ (DescentSortedRoster.indexed order) dst₀ G₀ M₀ ∧
      Source (L₀).counts ((L₀).dataCount order (A.roleValues v roles)) M₀ dst₀ ∧
      (∀l,Source ((L₀).want P₀ l) (fun (_ : Fin H₀) (_ : Fin G₀)=>Packed.token (some l)) M₀ dst₀) ∧
      (∀upper, A.priorStart v floor≤upper → ∀b : Bank,b.Fits w upper→H₀*chunks G₀ M₀≤b.size→
        Accessible P₀ b H₀ G₀ M₀ w upper) :=by
  obtain ⟨_,old,role,chip,pop⟩:=A.inlet_order v floor
  have pre:=old.trans (role.trans chip)
  have cuts:=A.inlet_frames v floor m safe
  have fieldLimit : (field₀).Fits w (A.priorStart v floor) :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt safe.venue.space,le_rfl⟩
  have addr:=ports field₀ fieldLimit A.clip.core.rowRoom
  have later (upper : ℕ) (le : A.priorStart v floor≤upper) (b : Bank)
      (usable : b.Fits w upper) (size : H₀*chunks G₀ M₀≤b.size) : Accessible P₀ b H₀ G₀ M₀ w upper :=by
    have a:=RoleControl.Layout.accessible_after addr le
    exact ⟨a.ids,a.idsRoom,a.roster,a.rosterRoom,a.offsets,a.offRoom,a.chunks,a.chunkRoom,usable,size⟩
  have reached:=RoleControl.Layout.previous_mounted addr (DescentSortedRoster.indexed order)
    (A.clipped_before_count v floor m safe) mounted
  have readable (x : Fin A.previous.blocks) : Accessible P₀ (A.labels v floor x) H₀ G₀ M₀ w (L₀).base :=by
    have placed:=(A.roleLayout v).placed (A.roleStart v floor) (chip.trans_lt (pop.trans_lt safe.ceiling)) x
    apply later _ pre _ ⟨placed.1.1,placed.1.2.1,placed.1.2.2.trans chip⟩ placed.2
  have out:=(L₀).issued P₀ (A.labels v floor) someBlock (A.chipTape v floor m) order (A.roleValues v roles) readable reached
    (fun x=>A.role_before_count v floor m safe x (roles x) positive (early x) (capacity x) (before x)) safe.ceiling
  refine ⟨?_,out.2.1,out.2.2,later⟩
  exact RoleControl.Layout.previous_mounted addr (DescentSortedRoster.indexed order)
    (fun i lo=>(cuts.count i (lo.trans_le pre)).trans (A.clipped_before_count v floor m safe i lo)) mounted

theorem venue_final {b : ℕ} (safe : A.Room v floor w) («fields» : Fin H₀→Fin G₀→Cell b)
    (read : Reads field₀ «fields» M₀ (A.clippedTape v floor m)) : Reads field₀ «fields» M₀ dst₀ :=by
  obtain ⟨_,j,k,l,_⟩:=A.inlet_order v floor
  let f:=A.inlet_frames v floor m safe
  apply reads_through read (show (field₀).base+(field₀).size≤A.priorStart v floor from le_rfl) A.clip.core.rowRoom
  intro i hi
  exact (f.count i (hi.trans_le (j.trans (k.trans l)))).trans (A.clipped_before_count v floor m safe i hi)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
