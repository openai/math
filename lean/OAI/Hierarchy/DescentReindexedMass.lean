import OAI.Hierarchy.DescentNetworkReindex
import OAI.Hierarchy.DescentStageMeasures

namespace OAI
/-! # Site and block charges under physical permutations -/
namespace Hierarchy.DescentSixParty.PhysicalRename
open Computability.BorderVNP.Crossing DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {d : ℕ} {P : Type} {bits : P→ℕ}
variable (A : MarkedWorld F d P bits) (site : Equiv.Perm A.graph.Site) (edge : Equiv.Perm A.graph.Edge)

omit [Field F] in
theorem siteUnits {T : Type*} (hub : A.graph.Site→Bool) (rec : A.graph.Site→List T) (wire β hist : ℕ)
    (v : A.graph.Site) : (world A site edge).siteUnits (hub ∘ site.symm) (rec ∘ site.symm) wire β hist (site v)=
      A.siteUnits hub rec wire β hist v := by
  symm
  unfold MarkedWorld.siteUnits
  refine congrArg₂ (·+·) (congrArg₂ (·+·) ?_ ?_) ?_
  · apply Fintype.sum_equiv edge
    intro i
    simp only [world,src,width]
    have hit : (site v=site (A.graph.src i)) ↔ v=A.graph.src i := site.injective.eq_iff
    change _=if site v=site (A.graph.src i) then wire*A.graph.width i*
      (if hub (site.symm (site (A.graph.src i))) then β else 1) else 0
    simp only [hit,site.symm_apply_apply]
  · apply Fintype.sum_equiv edge
    intro i
    simp only [world,dst,width]
    have hit : (site v=site (A.graph.dst i)) ↔ v=A.graph.dst i := site.injective.eq_iff
    change _=if site v=site (A.graph.dst i) then wire*A.graph.width i*
      (if hub (site.symm (site (A.graph.dst i))) then β else 1) else 0
    simp only [hit,site.symm_apply_apply]
  · exact congrArg (fun t=>hist*(rec t).length) (site.symm_apply_apply v).symm

omit [Field F] in
theorem blockMass {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (pos : A.graph.Site→V)
    (block : A.graph.Site→Block k) (full moved : A.graph.Site→ℕ)
    (weights : ∀u,moved (site u)=full u) (v : V) (x : Block k) :
    StarKeys.blockMass (world A site edge).graph (pos ∘ site.symm) (block ∘ site.symm) moved v x=
      StarKeys.blockMass A.graph pos block full v x := by
  symm
  unfold StarKeys.blockMass
  apply Fintype.sum_equiv site
  intro u
  change _=if pos (site.symm (site u))=v ∧ block (site.symm (site u))=x then moved (site u) else 0
  rw [site.symm_apply_apply,weights]

end
end Hierarchy.DescentSixParty.PhysicalRename

end OAI
