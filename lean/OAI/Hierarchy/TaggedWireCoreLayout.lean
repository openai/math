import OAI.Hierarchy.TaggedWireRowGraph
import OAI.Hierarchy.TaggedWireSettledLayout
import OAI.Hierarchy.TaggedWireCommodityGraphs

namespace OAI
/-! # The ordered physical walks of the mounted core board -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe
open scoped Classical BigOperators
variable {K r : ℕ}

theorem filled_ends (A : PortGraph (Fin K) (Fin r)) (pad : Chord K) (i : Fin r)
    (diff : A.tail i≠A.head i) :
    ((rowGraph (filledChord A pad)).tail i=A.tail i ∧ (rowGraph (filledChord A pad)).head i=A.head i) ∨
    ((rowGraph (filledChord A pad)).tail i=A.head i ∧ (rowGraph (filledChord A pad)).head i=A.tail i) := by
  by_cases h:A.tail i<A.head i <;> simp [rowGraph,filledChord,orderedChord,h,diff]

end Hierarchy.WireTelescope

namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope
open scoped Classical BigOperators

variable {S : PurchaseSampler} {h d k K edges : ℕ}

theorem different (π : Equiv.Perm (Fin (2^h))) (e : Edges S h d k) :
    (ends π e).1≠(ends π e).2 := by
  rcases e with f|⟨⟨p,t⟩,l⟩
  · rcases f with ⟨c,l⟩|f
    · simp [ends,freeEnds]
    · rcases f with ⟨c,a,s,t⟩|f
      · intro eqn
        have layer : some (a.val.1,s)=some (a.val.2,t) := congrArg Prod.snd eqn
        have eq : a.val.1=a.val.2 := congrArg Prod.fst (Option.some.inj layer)
        exact a.property.ne eq
      · rcases f with ⟨e,l⟩|⟨⟨t,g,o,i⟩,l⟩
        · intro eqn
          have same : e.val.1=e.val.2 := congrArg Prod.fst eqn
          exact e.property.2.ne (congrArg (Fintype.equivFin (Columns h d)) same)
        · simp [ends,freeEnds,inputCol,outputCol]
  · simp [ends,inputCol,outputCol]

section
variable {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
variable (B : Mount (S:=S) π place edges) (injective : Function.Injective place) (pad : Chord K)

include injective in
theorem Mount.core_order (e : Edges S h d k) :
    ((rowGraph (filledChord B.actual pad)).tail (B.row e)=(graph π place).tail e ∧
      (rowGraph (filledChord B.actual pad)).head (B.row e)=(graph π place).head e) ∨
    ((rowGraph (filledChord B.actual pad)).tail (B.row e)=(graph π place).head e ∧
      (rowGraph (filledChord B.actual pad)).head (B.row e)=(graph π place).tail e) := by
  have valid : B.actual.tail (B.row e) ≠ B.actual.head (B.row e) := by
    rw [B.tail,B.head]
    exact injective.ne (different π e)
  simpa only [B.tail,B.head] using filled_ends B.actual pad (B.row e) valid

def Mount.matrixLayout : SettledMatrix.Layout K edges (Commodity (Fin (2^h)) (Stages h d) k) (Columns h d × Fin k) where
  edge := filledChord B.actual pad
  goods := commodityGraph π place
  reserve := catalystGraph place
  goodsDistinct := commodityGraph_distinct π place injective
  reserveDistinct := catalystGraph_distinct place injective
  core := B.ordinary
  center := B.centers
  corePath i := unordered_walk (graph π place) _ B.row (B.core_order injective pad) (commodity_walk (S:=S) π place 0 i).1
  centerPath c := unordered_walk (graph π place) _ B.row (B.core_order injective pad) (catalyst_walk (S:=S) π place 0 c).1

end
end Hierarchy.ProbeStage.CoreBoard

end
end OAI
