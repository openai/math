import OAI.ThreeFlat.Diagonal.PhysicalChargeArray
import OAI.ThreeFlat.Diagonal.PhysicalShrinkCharges
import OAI.ThreeFlat.Diagonal.CompressorIncidentAddresses
import OAI.ThreeFlat.Diagonal.CompressorHalfValues

namespace OAI
/-! # Site ordinals and copy counts through native shrink casts -/
namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage MotifKernel PhysicalShrink
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

/-- An ordinal statement survives the degree and lane casts of the physical move. -/
private def CopiesAt {d l D rem : ℕ} {A : State d l} {R : Move F A D rem}
    (C : R.ShrinkSiteCopies) (G : ℕ→ℕ→ℕ→Prop) : Prop :=
  ∀i v,G i.val (Halves.siteNumber (R.next i).order ((R.next i).chart.symm v)) (C.copies i v)

private theorem copiesAt_degree {d l E D rem : ℕ} {A : State d l} (e : E=D)
    (R : Move F A E rem) (C : R.ShrinkSiteCopies) (G : ℕ→ℕ→ℕ→Prop) (h : CopiesAt C G) :
    CopiesAt (copiesDegree e R C) G := by cases e;exact h

private theorem copiesAt_lanes {d l l' D rem : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D rem) (C : R.ShrinkSiteCopies)
    (G : ℕ→ℕ→ℕ→Prop) (h : CopiesAt C G) :
    CopiesAt (copiesLanes e A R C) G := by cases e;exact h

open private occupiedCopiesAt chosenLayout from OAI.ThreeFlat.Diagonal.PhysicalShrinkCharges

private theorem shrink_copy_siteNumber {B : Type} [Fintype B] {t rem : ℕ}
    (order : B ≃ Fin (Fintype.card B)) (v : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord rem)) :
    Halves.siteNumber (productOrder order (tagOrdinal t)) ((v.1,v.2.1),v.2.2) =
      Incidents.siteNumber order v := by
  simp [Halves.siteNumber,Incidents.siteNumber,productOrder,finProdFinEquiv_apply_val]; ring

section CopyOrdinal
attribute [local irreducible] Finset.sum Finset.univ Fintype.card Fintype.equivFin
  ShrinkMotif.chooseWidths PhysicalShrink.r occupiedCopiesAt chosenLayout
  shrinkingGraph SlotRefinement.actualWidth

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem shrinkMove_copiesAt {d lanes rem h t D : ℕ} (T : ShrinkMotif.Table F)
    (A : State d lanes) (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord h × BitWord t × BitWord rem)
    (P : PackingData A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset) (hd : 0<d) (hD : 0<D)
    (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D≤1/1024) (tagSize : 1<2^t)
    (code : Arc A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) (G : ℕ→ℕ→ℕ→Prop)
    (verify : ∀ (i : Fin (Fintype.card (shrinkBranches T A u P hd code)))
      (v : Computability.VPVNP.Compression.Site A.Base (BitWord t) (BitWord rem)),
      let hc : 2≤2*d+1 := by omega
      let hist := (Fintype.equivFin (shrinkBranches T A u P hd code)).symm i
      let lay := ShrinkMotif.chooseWidths (issued T P (oldWidth A u) code hc hist)
      G i.val (Incidents.siteNumber A.order v)
        (∑ a : Active (partySite P lay) v, PhysicalShrink.r T P (oldWidth A u) code hc a.val)) :
    CopiesAt (R := shrinkMove T A u P agree good hd hD small tagSize code order)
      (shrinkMove_siteCopies T A u P agree good hd hD small tagSize code order) G := by
  have elected (i : Fin (Fintype.card (shrinkBranches T A u P hd code)))
      (v : Computability.VPVNP.Compression.Site A.Base (BitWord t) (BitWord rem)) :
      G i.val (Incidents.siteNumber A.order v) (occupiedCopiesAt T A u P hd code i v) := by
    unfold occupiedCopiesAt Local.activeCopiesAt chosenLayout
    have known := verify i v
    dsimp only at known
    refine (congrArg (G i.val (Incidents.siteNumber A.order v)) ?_).mp known
    apply Finset.sum_congr _ (fun _ _ => rfl)
    exact congrArg (fun f : Fintype _ => @Finset.univ _ f) (Subsingleton.elim _ _)
  unfold shrinkMove_siteCopies
  apply copiesAt_degree (e := degree_eq (by omega : 2≤2*d+1) hd hD)
  intro i v
  change G i.val (Halves.siteNumber (productOrder A.order (tagOrdinal t)) ((v.1,v.2.1),v.2.2))
    (occupiedCopiesAt T A u P hd code i v)
  rw [shrink_copy_siteNumber]
  exact elected i v

end CopyOrdinal

private def sitesAfterCast {d i j : ℕ} (e : i=j) (A : State d i) :
    A.Site ≃ (e ▸ A : State d j).Site := by cases e;exact Equiv.refl _

private theorem sitesAfterCast_number {d i j : ℕ} (e : i=j) (A : State d i) (v : A.Site) :
    let B := (e ▸ A : State d j)
    Halves.siteNumber B.order (B.chart.symm (sitesAfterCast e A v)) =
      Halves.siteNumber A.order (A.chart.symm v) := by cases e;rfl

private def ParentAt {d l D r : ℕ} {A : State d l} (R : Move F A D r)
    (G : ℕ→ℕ→ℕ→Prop) : Prop :=
  ∀i v,G i.val (Halves.siteNumber A.order (A.chart.symm v))
    (Halves.siteNumber (R.next i).order ((R.next i).chart.symm (R.parent i v)))

private theorem parentAt_degree {d l E D r : ℕ} {A : State d l} (e : E=D)
    (R : Move F A E r) (G : ℕ→ℕ→ℕ→Prop) (h : ParentAt R G) :
    ParentAt (e ▸ R : Move F A D r) G := by cases e;exact h

private theorem parentAt_lanes {d l l' D r : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D r) (G : ℕ→ℕ→ℕ→Prop) (h : ParentAt R G) :
    ParentAt (Move.recastInputLanes e A R) G := by cases e;exact h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem shrinkMove_parentAt {d lanes r h t D : ℕ} (T : ShrinkMotif.Table F)
    (A : State d lanes) (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord h × BitWord t × BitWord r)
    (P : PackingData A.Base (BitWord h) (BitWord t) (BitWord r) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset) (hd : 0<d) (hD : 0<D)
    (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D≤1/1024) (tagSize : 1<2^t)
    (code : Arc A.Base (BitWord h) (BitWord t) (BitWord r) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) (G : ℕ→ℕ→ℕ→Prop)
    (verify : ∀ (i : Fin (Fintype.card (shrinkBranches T A u P hd code))) (v : A.Site),
      let hc : 2≤2*d+1 := by omega
      let hist := (Fintype.equivFin (shrinkBranches T A u P hd code)).symm i
      let lay := ShrinkMotif.chooseWidths (issued T P (oldWidth A u) code hc hist)
      G i.val (Halves.siteNumber A.order (A.chart.symm v))
        (Incidents.siteNumber A.order (P.placement lay (StageAddress.splitSite u (A.chart.symm v))))) :
    ParentAt (shrinkMove T A u P agree good hd hD small tagSize code order) G := by
  unfold shrinkMove
  apply parentAt_degree
  intro i v
  let hc : 2≤2*d+1 := by omega
  let hist := (Fintype.equivFin (shrinkBranches T A u P hd code)).symm i
  let lay := ShrinkMotif.chooseWidths (issued T P (oldWidth A u) code hc hist)
  let y := P.placement lay (StageAddress.splitSite u (A.chart.symm v))
  change G i.val _ (Halves.siteNumber (productOrder A.order (tagOrdinal t)) ((y.1,y.2.1),y.2.2))
  have row : Halves.siteNumber (productOrder A.order (tagOrdinal t)) ((y.1,y.2.1),y.2.2) =
      Incidents.siteNumber A.order y := by
    simp [Halves.siteNumber,Incidents.siteNumber,productOrder,finProdFinEquiv_apply_val]; ring
  rw [row]
  exact verify i v


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
