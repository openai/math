import OAI.Hierarchy.TaggedWireSettledLayout
import OAI.Hierarchy.TaggedWireRouteOrientation

namespace OAI
/-! # An explicit signed-site operator for the paid, commodity and reserve reporter -/

noncomputable section
namespace Hierarchy.WireTelescope.SettledMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor AdaptiveProbe
open scoped Classical BigOperators

variable {S r : ℕ} {I A : Type} [Fintype I] [Fintype A] {F : Type*} [Field F]

namespace Layout
variable (B : Layout S r I A)

theorem installed (fixed : Fin r→ℕ) (stock : I→ℕ) (reserved used : A→ℕ) :
    installedWidths B.family (bits fixed stock reserved used) =
      installedWidths B.edge fixed+B.goods.chordWidths stock+B.reserve.chordWidths (fun i=>reserved i-used i) := by
  let num := numbered (r:=r) (I:=I) (A:=A)
  unfold installedWidths
  change (∑ i,available fixed stock reserved used (num i) • unitChord (B.original (num i)))=_
  rw [num.sum_comp (fun t=>available fixed stock reserved used t • unitChord (B.original t))]
  simp only [Source,Fintype.sum_sum_type,available,original,Sum.elim_inl,Sum.elim_inr,
    PortGraph.chordWidths,fun i=>oriented_width B.goods i (B.goodsDistinct i) (stock i),
    fun i=>oriented_width B.reserve i (B.reserveDistinct i) (reserved i-used i),add_assoc]

theorem measured (fixed : Fin r→ℕ) (stock : I→ℕ) (reserved used : A→ℕ) (e : Fin r) :
    routeLoad B.routes (bits fixed stock reserved used) e=
      fixed e+routeLoad B.core stock e+routeLoad B.center (fun i=>reserved i-used i) e := by
  let num := numbered (r:=r) (I:=I) (A:=A)
  change (∑ i,(B.steps (num i)).count e*available fixed stock reserved used (num i))=_
  rw [num.sum_comp (fun t=>(B.steps t).count e*available fixed stock reserved used t)]
  have paid : (∑ j : Fin r,[j].count e*fixed j)=fixed e := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ different
      simp [List.count_cons_of_ne different]
    · simp
  simp only [Source,Fintype.sum_sum_type,steps,available,Sum.elim_inl,Sum.elim_inr,
    oriented_count,routeLoad,paid,add_assoc]

/-- A physically identified terminal term: the assigned operators in this
matrix only copy matching bits, using the actual native occurrence order. -/
def operator (fixed : Fin r→ℕ) (stock : I→ℕ) (reserved used : A→ℕ)
    {n : ℕ} (ord : Fin n≃Σi,Fin (B.routes i).length) :=
  chordRouter (F:=F) B.family B.edge B.routes (bits fixed stock reserved used) ord (fun _i=>B.paths _)

theorem action (fixed : Fin r→ℕ) (stock : I→ℕ) (reserved used : A→ℕ)
    {n : ℕ} (ord : Fin n≃Σi,Fin (B.routes i).length)
    (x : ∀s,State (installedWidths B.family (bits fixed stock reserved used)) s) :
    (raw F _).coeff x =
      ∑ y : ∀e,Fin (2^(routeLoad B.routes (bits fixed stock reserved used) e)),
        ∏ s,B.operator fixed stock reserved used ord s (x s)
          (readEdges B.edge (routeLoad B.routes (bits fixed stock reserved used)) y s) :=
  (chordRouter_action B.family B.edge B.routes _ ord (fun _i=>B.paths _) x).trans (act_edge_words ..)

end Layout
end Hierarchy.WireTelescope.SettledMatrix

end
end OAI
