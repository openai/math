import OAI.Hierarchy.DescentTerminalBundleRows
import OAI.Hierarchy.DescentRestrictedPrivateCount

namespace OAI
/-! # Scalar public numbering preserves the genuine private-word count over all reached homes -/
namespace Hierarchy.DescentTerminalBundleRows
open DescentTerminalBoundaryBasis DescentTerminalGraphPositions DescentBundleHistory DescentKernelHistory
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {P U : Type} [Fintype P] {D S p t : ℕ} {bw : P→ℕ}
    (G : Network D P bw) (L : Order G S p) (hp : 0<p)

theorem numbered_used (v : G.Site) (rank : Boundary G v↪ℕ) (r : Recipe U (DescentTerminalBoundaryBasis.SiteRef (p:=p) G v))
    (code : U→Fin t) (h:r.Hidden) : (DescentTerminalBoundaryBasis.numbered G hp v rank r code).Used h↔r.Used h := by
  constructor
  · rintro ⟨u,j,hit⟩
    refine ⟨u,j,?_⟩
    change (r.operand u j).map _ id=.inr h at hit
    cases e:r.operand u j with
    | inl z=>simp [e] at hit
    | inr x=>
      have hx : x=h:=by simpa [e] using hit
      simp [hx]
  · rintro ⟨u,j,hit⟩
    exact ⟨u,j,by simp [DescentTerminalBoundaryBasis.numbered,hit]⟩

theorem numbered_words (v : G.Site) (rank : Boundary G v↪ℕ) (r : Recipe U (DescentTerminalBoundaryBasis.SiteRef (p:=p) G v))
    (code : U→Fin t) : Fintype.card (DescentTerminalBoundaryBasis.numbered G hp v rank r code).UsedWord=Fintype.card r.UsedWord :=
  Fintype.card_congr (Equiv.subtypeEquivRight (numbered_used G hp v rank r code))

/-- The physical census starts before global public addressing, restricts unused
summation words in place, and counts each retained word at its actual owning site. -/
theorem private_rows_volume (r : ∀v:G.Site,Recipe U (DescentTerminalBoundaryBasis.SiteRef (p:=p) G v))
    (birth : ∀v,(r v).Node ↪ ℕ) (code:U→Fin t) :
    (∑i,∑v,Fintype.card (recipes L (fun v=>(r v).restricted) hp birth code i v).UsedWord)=
      ∑v:G.Site,Fintype.card (r v).UsedWord := by
  calc
    _ = ∑i,∑v:Fin (L.site i).nodes,Fintype.card (r (L.node i v)).UsedWord := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro v _
      exact (numbered_words G hp _ _ _ code).trans (DescentTerminalVertexFields.restricted_words _)
    _ = ∑i,∑v : L.Nodes i,Fintype.card (r v.val).UsedWord :=
      Finset.sum_congr rfl (fun i _=>(L.nodes i).symm.sum_comp (fun v=>Fintype.card (r v.val).UsedWord))
    _ = _ := Fintype.sum_fiberwise L.home (fun v=>Fintype.card (r v).UsedWord)

end
end Hierarchy.DescentTerminalBundleRows

end OAI
