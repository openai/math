import OAI.Computability.NearSquareRoot.SynchronizedBatchPhaseRead
import OAI.Computability.NearSquareRoot.PrecisionRoutedWalsh

/-! # Preparing the scalar coefficient selected by a physical microinstruction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Staff Strip Carry ShortFourier.BatchWord

variable {J : Type} {s : Regime J} {precision micro activeCount n : J → ℕ}

private theorem eqMicro (M : Realizes s micro) (t : ℕ) : Classified s (fun j => micro j = t) := by
  have D := (M.minused (.fix t)).plus ((Realizes.fix t).minused M)
  have H := D.below (.fix 1)
  convert H using 1
  funext j
  apply propext
  omega

/-- Compute the round of the addressed routed phase from the microinstruction number. -/
theorem phaseRound_figure (M : Realizes s micro) :
    Figure s (fun j => (phaseRound (micro j)).val) := by
  have R := (Figure.natural 0).variant ((Figure.natural 1).variant (.natural 2) (eqMicro M 5)) (eqMicro M 3)
  convert R using 1
  funext j
  by_cases h : micro j = 3 <;> by_cases h' : micro j = 5 <;> simp [phaseRound, h, h']

/-- Dispatch directly from the stream's microinstruction field. The direct
case uses the placed table; routed diagonal slots use the active/idle coefficients. -/
theorem Prepared.phaseField (P : Realizes s precision) (M : Realizes s micro) (V : Figure s activeCount)
    (bit : J → Fin 2) (pair : (j : J) → Fin (n j))
    (B : Figure s (fun j => (bit j).val)) (Q : Figure s (fun j => (pair j).val))
    {placed : J → ℂ} (Z : Prepared s precision placed) :
    Prepared s precision (fun j => phaseField (micro j) (activeCount j) (bit j) (pair j) (placed j)) :=
  Prepared.conditional (eqMicro M 0) Z
    (Prepared.routedWalsh P (fun j => phaseRound (micro j)) bit pair (phaseRound_figure M) B Q V)

/-- A fully charged phase computation whenever the axis, local address and
ranked pair fields of an instruction are supplied by the address decoder. -/
theorem preparePhaseField {q : J → SlotQuery} (H : SlotQuery.Available s q)
    {start count row col : J → ℕ} (S : Realizes s start) (V : Realizes s count)
    (Y : Realizes s row) (X : Realizes s col) (R : Realizes s (fun j => 2^(q j).width))
    (M : Realizes s micro) (bit : J → Fin 2) (pair : (j : J) → Fin (n j))
    (B : Figure s (fun j => (bit j).val)) (Q : Figure s (fun j => (pair j).val)) :
    Prepared s (fun j => (q j).bits) (fun j => phaseField (micro j) (count j * 2^(q j).width)
      (bit j) (pair j) (placedCoefficient (q j) (start j) (count j) (row j) (col j))) :=
  Prepared.phaseField H.bits M (Figure.of_spoken (V.times R)) bit pair B Q (preparePlacedSlot H S V Y X R)

end PhaseTable

end NearSquareRoot
end Computability
end OAI
