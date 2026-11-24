import OAI.Computability.VPVNP.CompressorSelectedTerms
import OAI.Computability.VPVNP.CompressorShrinkMotifOrder
import OAI.Computability.VPVNP.CompressorRecordScores

/-!
# Layout scores from the selected term records

For each motif the row stores its common repetition count and the payload
width of each of its eight supply coordinates. Adding selector bits recovers
the widths entering the two competing layout energies. Reindexing the sum by
the physical motif scan order proves that a strict comparison of the two
integer totals selects exactly the compressor's common layout.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedScore

open Compression ShrinkMotif ShrinkEnergy MotifConversion BurstRAM PairSimulation.LocalHistory
open scoped Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))

/-- The physical scan order of motifs used to index the selected term records. -/
abbrev motifOrder : Order X.packingData.Motif := ⟨Fintype.card X.packingData.Motif, ShrinkMotifOrder.entries X⟩
/-- Enumerate the eight supply coordinates as a choice of layout side and one of its four
coordinates. -/
def supplyOrder : Order (Bool × Fin 4) := Order.prod ⟨2, finTwoEquiv⟩ (Order.fin 4)
/-- An admissible shrinking choice for every motif of the current packing. -/
abbrev Selection := ∀ m, X.packingData.ShrinkChoice X.shrinkNumber X.packingWidth B.shrink m

/-- The contiguous supply coordinate of one layout and role edge. -/
def coordinate (l : Bool) (t : Fin 4) : Fin 8 := finProdFinEquiv (finTwoEquiv.symm l,t)

theorem coordinate_index (l : Bool) (t : Fin 4) :
    (coordinate l t).val = l.toNat * 4 + t.val := by
  cases l <;> fin_cases t <;> decide

theorem supplyCoordinate (l : Bool) (t : Fin 4) : supplyOrder.entries (coordinate l t) = (l,t) := by
  change (finTwoEquiv.prodCongr (Equiv.refl _)) (finProdFinEquiv.symm (finProdFinEquiv (finTwoEquiv.symm l,t))) = _
  simp

/-- The established term readback predicate, over the actual filtered old arc list. -/
def Stored (s : Selection B X) (base : Fin (motifOrder X).length → Word w) (mem : Memory w) : Prop :=
  ∀ i, let m := (motifOrder X).entries i
    TermRecordScan.Fields B.shrink supplyOrder.entries demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m) (s m).val (base i) mem

/-- Read a selected coordinate's payload width and add the selector bits contributed by each
repetition in its motif row. -/
def widthAt (base : Fin (motifOrder X).length → Word w) (mem : Memory w)
    (i : Fin (motifOrder X).length) (l : Bool) (t : Fin 4) : ℕ :=
  (mem ((base i).val+2+(coordinate l t).val)).val + (mem ((base i).val+1)).val * B.shrink.selectorBits

theorem widthAt_eq (s : Selection B X) (base : Fin (motifOrder X).length → Word w) (mem : Memory w)
    (h : Stored B X s base mem) (i : Fin (motifOrder X).length) (l : Bool) (t : Fin 4) :
    widthAt B X base mem i l t =
      X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s ((motifOrder X).entries i) l t := by
  obtain ⟨_,hu,hv⟩ := h i
  rw [widthAt, hu, hv (coordinate l t)]
  rw [supplyCoordinate]
  rfl

/-- The weighted sum of squared selected widths over all motifs and four supply coordinates on
one layout side. -/
def score (base : Fin (motifOrder X).length → Word w) (mem : Memory w) (l : Bool) : ℕ :=
  ∑ t : Fin 4, ∑ i : Fin (motifOrder X).length, MotifAdmission.weight relativeMass t *
    widthAt B X base mem i l t ^ 2

theorem score_eq (s : Selection B X) (base : Fin (motifOrder X).length → Word w) (mem : Memory w)
    (h : Stored B X s base mem) (l : Bool) :
    score B X base mem l = layoutScore relativeMass
      (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s) l := by
  unfold score layoutScore MotifAdmission.energy
  rw [Finset.sum_comm]
  apply Fintype.sum_equiv (motifOrder X).entries
  intro i
  simp only [widthAt_eq B X s base mem h]

/-- The bit written on a strict improvement is the actual term-dependent shrinking layout. -/
theorem chosenLayout_eq (s : Selection B X) (base : Fin (motifOrder X).length → Word w) (mem : Memory w)
    (h : Stored B X s base mem) :
    decide (score B X base mem true < score B X base mem false) =
      X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s := by
  rw [score_eq B X s base mem h, score_eq B X s base mem h]
  apply selectLayout_eq relativeMass relativeMass_pos
  unfold equalArcMass
  exact div_pos one_pos (mul_pos (Nat.cast_pos.mpr (Fintype.card_pos (α := Position X.Base (BitWord a) (BitWord (packingTagBits (2^a))) (BitWord g) (2*2^a+1))))
    (Nat.cast_pos.mpr (Nat.two_pow_pos a)))

end CompressorRecords.SelectedScore

end

end VPVNP
end Computability
end OAI
