import OAI.Hierarchy.DescentSeedLinkFields

namespace OAI
/-! # Every paid seed coordinate is occupied -/
namespace Hierarchy.DescentPaidResidentCount.Seed
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentInitialHost DescentSeedRoot DescentColonies Catalyst
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
   {k cp pins wire s z H w M b : ℕ} (X : Approximation F cp pins)
   {c : (initialGroup X S.copies s).Choice}
   {r : Reached ((initialGroup X S.copies s).state c) G q ε S k 0 z 3 wire s}
   {digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k} (link : SeedLink X c r digits)
local notation "W" => (initialGroup X S.copies s).state c
local notation "V₀" => Fintype.card (Vertex X)

include link in
/-- Every seed vertex receives one copy at each old group and block. -/
theorem at_site (g : Fin (S.groupCount 0)) (v : r.V) (x : Block k) :
    ∃u : (W).graph.Site,r.placement.pos u=(g,v) ∧ r.placement.block u=x := by
  let assign:=fun u : (W).graph.Site=>(r.placement.pos u,r.placement.block u)
  have numbers := Fintype.card_congr digits
  have same : Fintype.card (W).graph.Site=Fintype.card ((Fin (S.groupCount 0)×r.V)×Block k) := by
    change Fintype.card (Σ _ : Fin S.copies,Vertex X)=_
    simp only [Fintype.card_prod,Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at numbers ⊢
    rw [link.hostSize]
    change S.copies=S.groupCount 0*2^k at numbers
    change S.copies*V₀=(S.groupCount 0*V₀)*2^k
    rw [numbers];ring
  obtain ⟨u,h⟩:=((Fintype.bijective_iff_injective_and_card assign).mpr ⟨r.valid.coordinates,same⟩).surjective ((g,v),x)
  exact ⟨u,congrArg Prod.fst h,congrArg Prod.snd h⟩

end
end Hierarchy.DescentPaidResidentCount.Seed

end OAI
