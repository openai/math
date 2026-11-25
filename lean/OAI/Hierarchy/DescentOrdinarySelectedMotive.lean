import OAI.Hierarchy.DescentDatedSelectedCableKey

namespace OAI
/-! Dependent transport from the emitted matcher's actual choice to the original chronological receipt. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)
local notation "A" => v.prior.placement
local notation "T" => (A).stage
local notation "post" n:arg => Reached (n).result v.gadget v.q v.ε v.schedule v.k (v.age+1)
  v.nextZ v.nextDegree v.wire v.hist

/-- The motive may use the full archive, the local node enumeration and the physical
pointer names obtained from this particular normalization and this particular link. -/
theorem AtSelected.on_ticket (picked:(v.prior.placement.stage.result v.nonnegative).Choice) (proof:HEq picked v.choice)
    (a:AtSelected v picked)
    (M:(u:ℝ)→(t:StageInput v.world v.gadget u v.ε)→(c:(t.result v.nonnegative).Choice)→
      (n:Normalize ((t.result v.nonnegative).state c))→(r:post n)→
      OrdinaryLink v.prior v.nonnegative t c n r→Prop)
    (observed:M _ T picked a.norm a.next a.link) :
    M v.u v.stage v.choice v.normalize v.target v.ticket :=by
  cases v with
  | mk d bits G S q u eps k date z degree wire hist nz nd W prior he t c n r ticket old reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue level b short payload unit profile seats =>
    obtain rfl:=ticket.sourceRate
    obtain rfl:=eq_of_heq ticket.placement
    have pickedEq : picked = c := eq_of_heq proof
    subst picked
    cases a with
    | mk n₁ r₁ link hnorm hnext ht =>
      have normEq : n₁ = n := eq_of_heq hnorm
      subst n₁
      have nextEq : r₁ = r := eq_of_heq hnext
      subst r₁
      have linkEq : link = ticket := eq_of_heq ht
      subst link
      exact observed

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
