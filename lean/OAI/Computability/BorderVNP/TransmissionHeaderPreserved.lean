import OAI.Computability.BorderVNP.TransmissionJointHeader
import OAI.Computability.BorderVNP.TransmissionPinsLoop
import OAI.Computability.BorderVNP.TransmissionSenderStable
import OAI.Computability.BorderVNP.RoutingISATableAddressImage
import OAI.Computability.BorderVNP.RoutingISATypedBatchMemory

/-! # Preserving the copied common header through the native evaluation stages -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open VPVNP.BurstRAM RoutingISA RoutingISA.Transmission

variable {w : ℕ} {dst : ℕ} {bits : List Bool} {m m' : Memory w}

/-- A physical operation preserves the common bits by leaving their addresses untouched. -/
theorem FlatAt.congr (h : FlatAt m dst bits)
    (eq : ∀ i : Fin bits.length, m' (dst+i.val) = m (dst+i.val)) : FlatAt m' dst bits :=
  fun i => (eq i).trans (h i)

/-- Pin preparation writes only the two pin arrays. -/
theorem FlatAt.prepare (h : FlatAt m dst bits) (L : Pins.Layout) (guess : ℕ → Bool) (k : ℕ)
    (index : DiagonalTallyRAM.separated dst bits.length L.ibase k)
    (pin : DiagonalTallyRAM.separated dst bits.length L.hbase L.width) :
    FlatAt (Pins.preparedMemory L guess m k) dst bits := by
  apply h.congr
  intro i
  have bound := i.isLt
  apply Pins.preparedMemory_other
  · intro j hj
    rcases index with left | right <;> omega
  · intro j _ active
    have small : j < L.width := active.2
    rcases pin with left | right <;> omega

/-- Building the actual routing schedule leaves the broadcast copy outside its four
writable arrays. -/
theorem FlatAt.schedule (h : FlatAt m dst bits) (l : TableLayout) (rows : ℕ → TableRow)
    (image : l.Image rows (readings m) (readings m'))
    (apart : ∀ i : Fin bits.length, ∀ a ∈ [TableArray.widths,.ordinals,.offsets,.used],
      ¬ l.contains a (dst+i.val)) : FlatAt m' dst bits := by
  apply h.congr
  intro i
  exact Fin.ext (image.outside _ (apart i _ (by simp)) (apart i _ (by simp))
    (apart i _ (by simp)) (apart i _ (by simp)))

/-- No selected transmission role writes a protected header address at any prefix. -/
theorem FlatAt.transmit (h : FlatAt m dst bits) (rows : ℕ → Range w) (self : Word w)
    (pub : Arg → Word w) (choices : ℕ → ℕ → Bool) (k : ℕ)
    (apart : ∀ j < k, ∀ i : Fin bits.length, (rows j).protectsCell self (dst+i.val)) :
    FlatAt (tableMemory rows self pub m choices k) dst bits :=
  h.congr fun i => tableMemory_protected rows self pub m choices k _ (fun j hj => apart j hj i)

/-- The cell argument preparer writes its scratch and output intervals and two call
fields for each task. All common-header words survive the actual chronology. -/
theorem FlatAt.cells (h : FlatAt m dst bits) (tasks : ℕ → TypedBatch.Task) (k : ℕ)
    (apart : ∀ j < k, ∀ i : Fin bits.length, (tasks j).Outside w (dst+i.val)) :
    FlatAt (TypedBatch.written m tasks k) dst bits :=
  h.congr fun i => TypedBatch.preserve m tasks (Nat.zero_le k) _ (fun j _ hj => apart j hj i)

/-- On the actual sparse table fold followed by the team's concrete cell-call batch,
the native tally decoder reads the same field words that were copied from the exterior. -/
theorem fields_after_ranges_cells {aux : List Bool} {xs : List (List Bool)} {extra : ℕ}
    (hw : 0 < w) (copy : FlatAt m dst (padded (spelling aux xs) extra))
    (rows : ℕ → Range w) (self : Word w) (pub : Arg → Word w) (choices : ℕ → ℕ → Bool)
    (ranges calls : ℕ) (tasks : ℕ → TypedBatch.Task)
    (away : ∀ j < ranges, ∀ i : Fin (padded (spelling aux xs) extra).length,
      (rows j).protectsCell self (dst+i.val))
    (cell : ∀ j < calls, ∀ i : Fin (padded (spelling aux xs) extra).length,
      (tasks j).Outside w (dst+i.val)) :
    DiagonalTallyBits.WordsAt (TypedBatch.written (tableMemory rows self pub m choices ranges) tasks calls)
      (dst+1+aux.length) xs :=
  fieldsAt_padded hw dst aux xs extra ((copy.transmit rows self pub choices ranges away).cells tasks calls cell)

end TeamContraction.JointHeader

end BorderVNP
end Computability
end OAI
