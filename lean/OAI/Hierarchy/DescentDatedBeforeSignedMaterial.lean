import OAI.Hierarchy.DescentDatedMaterialSockets
import OAI.Hierarchy.DescentDatedPriorHeaderRuns

namespace OAI
/-! The earlier physical rotor builds the live reverse ranks used by the ordinary material stage. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "H" => v.area.H
local notation "G" => v.signed.groups
local notation "M" => v.signed.lanes
local notation "D" => v.signed.degree
def beforeSignedMaterial (floor : ℕ) (parts adj : Bank) (w : ℕ) : NativePhase w :=
  let base:=v.donorEnd floor
  let header:=PriorHeader.phase H G M D base adj w
  let mat:=PriorHeader.endAddress H G M D base
  header.seq (v.materialAt mat parts (PriorHeader.reverseRank H G M D base) w)
theorem before_material_clock (floor : ℕ) (parts adj : Bank) (w : ℕ) :
    let base:=v.donorEnd floor
    let addr:=PriorHeader.endAddress H G M D base
    (v.beforeSignedMaterial floor parts adj w).ticks =
      (PriorHeader.phase H G M D base adj w).ticks+
      (v.materialAt addr parts (PriorHeader.reverseRank H G M D base) w).ticks :=rfl
theorem before_signed_any (floor : ℕ) (parts adj : Bank) {w : ℕ}
    (cover : PriorHeader.Room adj H G M D (v.donorEnd floor) w)
    (paid : v.MaterialRoom (v.materialStart floor) parts (PriorHeader.reverseRank H G M D (v.donorEnd floor)) w)
    (m : Memory w) : (v.beforeSignedMaterial floor parts adj w).Runs m ∧
    ∀j,j<v.donorEnd floor ∨ v.materialEnd floor≤j→(v.beforeSignedMaterial floor parts adj w).image m j=m j :=by
  let first:=PriorHeader.phase H G M D (v.donorEnd floor) adj w
  have mounted:=PriorHeader.any H G M D (v.donorEnd floor) adj cover m
  have post:=v.material_any paid (first.image m)
  have low:=PriorHeader.lower H G M D (v.donorEnd floor)
  have high:v.materialStart floor≤v.materialEnd floor:=by
    rw [materialEnd,v.material.translated];exact Nat.le_add_right ..
  refine ⟨NativePhase.seq_runs _ _ _ mounted.1 post.1,?_⟩
  intro j outside
  let b:=v.materialStart floor
  have before:v.donorEnd floor≤b:=low
  have right:j<b ∨ v.materialEnd floor≤j:=by rcases outside with h|h <;> omega
  have left:j<v.donorEnd floor ∨ b≤j:=by rcases outside with h|h <;> omega
  refine (post.2 j right).trans ?_
  change (PriorHeader.phase H G M D (v.donorEnd floor) adj w).image m j=m j
  rw [PriorHeader.phase_image]
  exact mounted.2 j left

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
