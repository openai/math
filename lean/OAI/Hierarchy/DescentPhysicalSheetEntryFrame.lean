import OAI.Hierarchy.DescentPhysicalMixedCapture

namespace OAI
/-! # Retaining the physical stem and trunk headers through all later candidate writers -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup DescentPackedColony DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "s" => (v).sheets
local notation "rbase" => ((v).remap b).endAddress
local notation "scene" => (v).front.trunkScene ((v).actorEnd b) ((v).issuedScene b u.earlier) u.sceneFits
local notation "front₀" => (v).front
local notation "cut₀" => (v).actorEnd b
local notation "old₀" => (v).issuedScene b u.earlier
local notation "donor₀" => (front₀).donorStart cut₀
local notation "mass₀" => (v).trunkEnd b
local notation "jointPhase" => (v).jointPhase b u.earlier w
local notation "pr₀" => (v).privateShape
local notation "oldPitch" => (front₀).contactLayout cut₀

theorem from_trunk_frame (ok : u.Ready) (m : Memory w) :
    ∀z,z<(v).trunkEnd b→u.sheetsEntry ok m z=(scene).image m z:=by
  let m₃:=(scene).image m
  obtain ⟨massRun,massCheap,massFrame⟩:=(v).contactShape.actual donor₀ mass₀
    (old₀).donor u.sceneFits.donor ok.donors ok.mass ok.projectionLanes ok.projectionBlocks m₃
  let massOut:=(v).contactShape.issuedImage donor₀ mass₀ (old₀).donor m₃
  obtain ⟨joinRun,joinFrame⟩:=(v).joint_any b u.earlier massOut ok.joints ok.packed
  let mid:=(jointPhase).image massOut
  have privateFits:=(v).private_inputs_fit b u.earlier ok.pages ok.privates
  let post:=(v).privatePhase b u.earlier ok.projectionLanes ok.projectionBlocks privateFits ok.privates
  obtain ⟨pRun,pKeep⟩:=(v).private_any b u.earlier mid ok.projectionLanes ok.projectionBlocks privateFits ok.privates
  obtain ⟨t₄,c₄,h₄⟩:=u.masked.any (post.image mid) (u.genuine_mask_previous ok.joints ok.masked) ok.masked
  obtain ⟨t₅,c₅,h₅⟩:=u.numbered.any rbase (u.masked.image (post.image mid)) ok.numbers
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ok.ordered
  have end_:=(u.masks_end)
  intro z hz
  exact (h₅ z (by omega)).trans
    ((h₄ z (by change z<(v).privateEnd b ∨ _;omega)).trans
    ((pKeep z (by omega)).trans
    ((joinFrame z (by omega)).trans
      (massFrame z (.inl hz)))))

theorem from_trunk_source (ok : u.Ready) (m : Memory w) {H G b₁ M : ℕ}
    (e : Expr) (values : Fin H→Fin G→Cell b₁)
    (fits : e.Fits w ((v).trunkEnd b)) (previous : Source e values M ((scene).image m)) :
    Source e values M (u.sheetsEntry ok m):=by
  intro z
  exact (eval_below e _ _ _ fits (u.from_trunk_frame ok m)).trans (previous z)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
