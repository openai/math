import OAI.ThreeFlat.RAM.HistoryFactorLibrary
import OAI.ThreeFlat.Diagonal.TraceCircuitPad

namespace OAI
/-! # Padding a history factor stream while retaining shared table IDs -/

namespace ThreeFlat.RAM.HistoryFactors

open Diagonal.TraceCircuit
variable {F : Type*} {p : ℕ} [Zero F] [One F]

/-- The original library is followed by the unary zero-test table and the unit table. -/
def Library.padded {N : BitNetwork F p} (L : Library N) (b u : ℕ) :
    Library (addPadding N b u) where
  count := L.count+2
  id := Fin.addCases (Fin.addCases (fun i => (L.id i).castAdd 2)
      (fun _ : Fin b => Fin.natAdd L.count 0)) (fun _ : Fin u => Fin.natAdd L.count 1)
  table := Fin.addCases L.table ![fun v => if v 0 then 0 else 1,fun _ => 1]
  correct := by
    intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · simpa only [addPadding, Fin.addCases_left, networkCells, Cell.lift] using L.correct j
      · simp only [addPadding, Fin.addCases_left, Fin.addCases_right]; rfl
    · simp only [addPadding, Fin.addCases_right]; rfl

@[simp] theorem padded_zero_table {N : BitNetwork F p} (L : Library N) (b u : ℕ)
    (v : Fin 3 → Bool) : (L.padded b u).table (Fin.natAdd L.count 0) v =
      if v 0 then 0 else 1 := by simp [Library.padded]

@[simp] theorem padded_unit_table {N : BitNetwork F p} (L : Library N) (b u : ℕ)
    (v : Fin 3 → Bool) : (L.padded b u).table (Fin.natAdd L.count 1) v = 1 := by
  simp [Library.padded]

/-- A fixed hidden capacity H and row capacity J consume exactly H old-or-padded bits
and J old, zero-test, or unit cells. -/
theorem fixed_capacities (N : BitNetwork F p) {H J : ℕ} (hh : N.internal ≤ H)
    (hj : N.cells + (H-N.internal) ≤ J) :
    let G := addPadding N (H-N.internal) (J-(N.cells+(H-N.internal)))
    G.internal = H ∧ G.cells = J := by
  change N.internal+(H-N.internal) = H ∧
    (N.cells+(H-N.internal))+(J-(N.cells+(H-N.internal))) = J
  constructor <;> omega

end ThreeFlat.RAM.HistoryFactors

end OAI
