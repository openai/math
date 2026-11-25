import OAI.Hierarchy.DescentOldHostBall
import OAI.Hierarchy.DescentNextCoordinates

namespace OAI
/-! # An ordinary host's ten-hop directory separates into an old host and a public shape -/
namespace Hierarchy.DescentHostDirectory
open DescentContacts DescentColonies
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V]

abbrev ShapeSlot := (ℕ×ℕ)×ℕ
def shapeStep (window slots : ℕ) (q : ShapeSlot) : Finset ShapeSlot :=
  possible q.1.1 q.1.2 window window ×ˢ Finset.range slots

def shapeReach (window slots : ℕ) : ℕ→ShapeSlot→Finset ShapeSlot
  | 0,q=>{q}
  | t+1,q=>(shapeReach window slots t q).biUnion (shapeStep window slots)

/-- Each hop chooses its old host and its shape independently; synchronizing the
two length-t paths reconstructs an actual path, including both length-zero cases. -/
theorem directory_product (near : V→Finset V) (window slots t : ℕ) (u v : Key V) :
    v∈directory near window slots t u ↔
      v.1∈DescentOrdinaryDonorHalo.around near t u.1 ∧ v.2∈shapeReach window slots t u.2 := by
  induction t generalizing v with
  | zero=>
    simp only [directory,DescentOrdinaryDonorHalo.around,shapeReach,Finset.mem_singleton]
    exact ⟨fun h=>⟨congrArg Prod.fst h,congrArg Prod.snd h⟩,fun h=>Prod.ext h.1 h.2⟩
  | succ t ih=>
    constructor
    · intro inDir
      obtain ⟨old,prev,step⟩:=Finset.mem_biUnion.mp inDir
      have both:=(ih old).1 prev
      obtain ⟨root,shape⟩:=Finset.mem_product.mp step
      exact ⟨Finset.mem_biUnion.mpr ⟨old.1,both.1,root⟩,Finset.mem_biUnion.mpr ⟨old.2,both.2,shape⟩⟩
    · rintro ⟨roots,shapes⟩
      obtain ⟨v₀,local₀,step₀⟩:=Finset.mem_biUnion.mp roots
      obtain ⟨v₁,local₁,step₁⟩:=Finset.mem_biUnion.mp shapes
      exact Finset.mem_biUnion.mpr ⟨(v₀,v₁),(ih (v₀,v₁)).2 ⟨local₀,local₁⟩,Finset.mem_product.mpr ⟨step₀,step₁⟩⟩

private theorem mutual_product (near : V→Finset V) (window slots t : ℕ) (u v : Key V) :
    (v∈directory near window slots t u ∧ u∈directory near window slots t v) ↔
      (v.1∈DescentOrdinaryDonorHalo.around near t u.1 ∧
        u.1∈DescentOrdinaryDonorHalo.around near t v.1) ∧
      (v.2∈shapeReach window slots t u.2 ∧ u.2∈shapeReach window slots t v.2) := by
  have forward := directory_product near window slots t u v
  have backward := directory_product near window slots t v u
  constructor
  · rintro ⟨outward,inward⟩
    obtain ⟨outHost,outShape⟩ := forward.mp outward
    obtain ⟨inHost,inShape⟩ := backward.mp inward
    exact ⟨⟨outHost,inHost⟩,outShape,inShape⟩
  · rintro ⟨⟨outHost,inHost⟩,outShape,inShape⟩
    exact ⟨forward.mpr ⟨outHost,outShape⟩,backward.mpr ⟨inHost,inShape⟩⟩

/-- Forward and reverse searches use only one fixed table of local shapes and one old-host roster. -/
theorem restricted_product [Fintype V] (near : V→Finset V) (window k slots : ℕ) (u v : Host V k slots) :
    v∈restrictedNear near window k slots u ↔
      (v.val.1∈DescentOrdinaryDonorHalo.around near 10 u.val.1 ∧
        u.val.1∈DescentOrdinaryDonorHalo.around near 10 v.val.1) ∧
      (v.val.2∈shapeReach window slots 10 u.val.2 ∧ u.val.2∈shapeReach window slots 10 v.val.2) := by
  unfold restrictedNear
  refine Finset.mem_filter.trans ?_
  exact (and_iff_right (Finset.mem_univ v)).trans (mutual_product near window slots 10 u.val v.val)

end
end Hierarchy.DescentHostDirectory

end OAI
