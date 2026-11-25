import OAI.ThreeFlat.Diagonal.PhysicalChargeFactor
import OAI.ThreeFlat.Diagonal.PhysicalIncidentWidth
import OAI.ThreeFlat.Diagonal.ShrinkActiveCopyBudget
import OAI.ThreeFlat.Diagonal.PhysicalStageBinary

namespace OAI
/-! # Native active records charged at the actual successor of the selected shrink -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking MotifKernel
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

def shrinkSiteCopyFactor (d : ℕ) : ℕ :=
  (8*d^2*2^(2*d+1))*shrinkCopyFactor (2*d+1) d

/-- Local motif copies on the selected successor, with the two counting bounds needed
by the chronological scan. Degree and lane casts transport both the data and the bounds. -/
structure Move.ShrinkSiteCopies {d l D L : ℕ} {A : State d l} (R : Move F A D L) where
  copies : ∀ t, (R.next t).Site → ℕ
  total : ∀ t, (∑ v, copies t v) ≤ 6*(d*A.positions+A.widthSum)
  local_le : ∀ t v, copies t v ≤ shrinkSiteCopyFactor d*(1+A.maxWidth)

def copiesDegree {d l D E r : ℕ} {A : State d l} (e : E=D) (R : Move F A E r) :
    R.ShrinkSiteCopies → (e ▸ R : Move F A D r).ShrinkSiteCopies := by
  cases e
  exact id

def copiesLanes {d l l' D rem : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D rem) :
    R.ShrinkSiteCopies → (Move.recastInputLanes e A R).ShrinkSiteCopies := by
  cases e
  exact id

section OccupiedCopies

variable {d lanes rem hbits tags : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
  (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord hbits × BitWord tags × BitWord rem)
  (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1))
  (hd : 0<d) (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1) ↪ ℕ)

private def chosenLayout (i : Fin (Fintype.card (shrinkBranches T A u P hd code))) : Bool :=
  let hist := (Fintype.equivFin (shrinkBranches T A u P hd code)).symm i
  ShrinkMotif.chooseWidths (PhysicalShrink.issued T P (oldWidth A u) code (by omega) hist)

private def occupiedCopiesAt (i : Fin (Fintype.card (shrinkBranches T A u P hd code)))
    (v : Site A.Base (BitWord tags) (BitWord rem)) : ℕ :=
  Local.activeCopiesAt P (chosenLayout T A u P hd code i) (PhysicalShrink.r T P (oldWidth A u) code (by omega)) v

section

attribute [local irreducible] chosenLayout PhysicalShrink.r Local.activeCopiesAt

set_option maxHeartbeats 800000 in
private theorem occupiedCopies_budget (i : Fin (Fintype.card (shrinkBranches T A u P hd code))) :
    Local.ActiveCopyBounds (d:=d) (c:=2*d+1) (V:=A.Base) (H:=BitWord hbits)
      (Tag:=BitWord tags) (L:=BitWord rem) P (chosenLayout T A u P hd code i)
      (PhysicalShrink.r T P (oldWidth A u) code (by omega)) (d*A.positions+A.widthSum)
      (shrinkCopyFactor (2*d+1) d*(1+A.maxWidth)) := by
  exact Local.active_copies_of_budget (d:=d) (c:=2*d+1) (V:=A.Base) (H:=BitWord hbits)
    (Tag:=BitWord tags) (L:=BitWord rem) P (chosenLayout T A u P hd code i)
    (PhysicalShrink.r T P (oldWidth A u) code (by omega)) _ _ (shrinkCopies_budget T A u P code (by omega) hd)

private theorem occupiedCopiesAt_bounds (i : Fin (Fintype.card (shrinkBranches T A u P hd code))) :
    (∑ v, occupiedCopiesAt T A u P hd code i v) ≤ 6*(d*A.positions+A.widthSum) ∧
    ∀ v, occupiedCopiesAt T A u P hd code i v ≤ shrinkSiteCopyFactor d*(1+A.maxWidth) := by
  have budget := occupiedCopies_budget T A u P hd code i
  unfold occupiedCopiesAt
  constructor
  · refine (Nat.le_of_eq ?_).trans budget.1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    exact congrArg (fun t : Fintype (Site A.Base (BitWord tags) (BitWord rem)) => @Finset.univ _ t)
      (Subsingleton.elim _ _)
  · intro v
    unfold shrinkSiteCopyFactor
    rw [Nat.mul_assoc (8*d^2*2^(2*d+1)) (shrinkCopyFactor (2*d+1) d) (1+A.maxWidth)]
    exact budget.2 v

end

private theorem occupiedCopiesAt_total (i : Fin (Fintype.card (shrinkBranches T A u P hd code)))
    {sites : Fintype (Site A.Base (BitWord tags) (BitWord rem))} :
    (@Finset.univ _ sites).sum (occupiedCopiesAt T A u P hd code i) ≤ 6*(d*A.positions+A.widthSum) := by
  refine (Nat.le_of_eq ?_).trans (occupiedCopiesAt_bounds T A u P hd code i).1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  exact congrArg (fun t : Fintype (Site A.Base (BitWord tags) (BitWord rem)) => @Finset.univ _ t)
    (Subsingleton.elim _ _)

end OccupiedCopies

section
attribute [local irreducible] occupiedCopiesAt chosenLayout PhysicalShrink.r
  ShrinkMotif.chooseWidths

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- The term ordinal selects the histogram and its layout. The sum uses the compact
occupied-motif rows of this same layout at this successor site. -/
def shrinkMove_siteCopies {d lanes rem hbits tags D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord hbits × BitWord tags × BitWord rem)
    (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P = changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset)
    (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
    (tagSize : 1<2^tags) (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (PhysicalShrink.parallel (2*d+1) d D) ↪ ℕ) :
    (shrinkMove T A u P agree good hd hD small tagSize code order).ShrinkSiteCopies := by
  unfold shrinkMove
  apply copiesDegree
  exact ⟨occupiedCopiesAt T A u P hd code,
    fun i => occupiedCopiesAt_total T A u P hd code i,
    fun i => (occupiedCopiesAt_bounds T A u P hd code i).2⟩

end

def shrinkRaw_siteCopies (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) ((2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem)))) :
    (shrinkRaw T s D rem hD small A).ShrinkSiteCopies := by
  unfold shrinkRaw
  apply shrinkMove_siteCopies

def shrinkBinary_siteCopies (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) : (shrinkBinary T s D rem hD small A).ShrinkSiteCopies := by
  unfold shrinkBinary
  apply copiesLanes
  exact shrinkRaw_siteCopies T s D rem hD small _

variable (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
  (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
  (A : State (2^s) (shrinkCharge s+rem))

local notation "R" => shrinkBinary T s D rem hD small A

/-- One record, both sets of incident half-ports, and the copies in the selected compact rows. -/
def shrinkBinaryCharge (t : Fin (R).rules.count) (v : ((R).next t).Site) : ℕ :=
  1+((R).next t).incidentWidth v+(shrinkBinary_siteCopies T s D rem hD small A).copies t v

def shrinkPeakFactor (s D : ℕ) := 1+2*D+shrinkSiteCopyFactor (2^s)

theorem shrinkBinaryCharge_sum (t : Fin (R).rules.count) :
    (∑ v, shrinkBinaryCharge T s D rem hD small A t v) ≤
      shrinkChargeFactor s*(A.positions+A.widthSum+((R).next t).positions+((R).next t).widthSum) := by
  let S := (R).next t
  let budget := A.positions+A.widthSum+S.positions+S.widthSum
  have ha : A.positions ≤ budget := by dsimp [budget]; omega
  have hb : A.widthSum ≤ budget := by dsimp [budget]; omega
  have hc : S.positions ≤ budget := by dsimp [budget]; omega
  have hd : S.widthSum ≤ budget := by dsimp [budget]; omega
  let C := shrinkBinary_siteCopies T s D rem hD small A
  have hm : (2^s)*A.positions + A.widthSum ≤ (2^s+1)*budget := by
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ ha) hb
  change (∑ v, (1+S.incidentWidth v+C.copies t v)) ≤ shrinkChargeFactor s*budget
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,S.sum_incidentWidth]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_one]
  calc
    _ ≤ budget + 2*budget + 6*((2^s+1)*budget) :=
      Nat.add_le_add (Nat.add_le_add hc (Nat.mul_le_mul_left 2 hd))
        ((C.total t).trans (Nat.mul_le_mul_left 6 hm))
    _ = _ := by unfold shrinkChargeFactor; ring

theorem shrinkBinaryCharge_le (t : Fin (R).rules.count) (v : ((R).next t).Site) :
    shrinkBinaryCharge T s D rem hD small A t v ≤
      shrinkPeakFactor s D*(1+A.maxWidth+((R).next t).maxWidth) := by
  let S := (R).next t
  let budget := 1+A.maxWidth+S.maxWidth
  have han : 1 ≤ budget := by dsimp [budget]; omega
  have h1 : 1+A.maxWidth ≤ budget := by dsimp [budget]; omega
  have h2 : S.maxWidth ≤ budget := by dsimp [budget]; omega
  let C := shrinkBinary_siteCopies T s D rem hD small A
  change 1+S.incidentWidth v+C.copies t v ≤ shrinkPeakFactor s D*budget
  calc
    _ ≤ budget + (2*D)*budget + shrinkSiteCopyFactor (2^s)*budget :=
      Nat.add_le_add (Nat.add_le_add han ((S.incidentWidth_le v).trans (Nat.mul_le_mul_left _ h2)))
        ((C.local_le t v).trans (Nat.mul_le_mul_left _ h1))
    _ = _ := by unfold shrinkPeakFactor; ring

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
