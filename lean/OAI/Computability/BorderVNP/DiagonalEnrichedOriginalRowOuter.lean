import OAI.Computability.BorderVNP.DiagonalEnrichedCompilationRow
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProcessor

/-! # Terminal row of an original port in the actual compiled outer machine

The source compiler provides the site-row displacement at every combining
stage. Its inner and outer row-major copy numbers give a fixed public sum of
these displacements, while each true histogram selects its own physical
terminal pack. This applies to the machine's public transcript and to the
equivalent packing history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open private flat_repeat from OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e}
variable {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
variable {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {w : ℕ} (C : SelectedSchedule.Compiled bits deep budget cap w)

local notation "Admit" => Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
  (shape := SelectedSchedule.boundaryShape S start) (w := w) budget)

/-- Displacement of one of the outer node's input bundles, obtained from its
successive digits in the actual allocated inner rectangles. -/
noncomputable def compiledOffset (S : Normalized.SiteSchedule e) (start t : ℕ) (i : Fin (fan S)) :=
  flatOffset (fun j (a : Fin S.fanIn) => a.val*(SelectedSchedule.before S start t j).sites) S.rounds i

set_option maxHeartbeats 1400000 in
/-- The genuine compiled machine reads the row of an original port at the
sum of its public copy displacements and the row in the selected leaf. -/
theorem compiledFlat_row (n : ℕ) (hn : n ≤ T) (flat : Fin ((fan S)^n) → Admit 0)
    (q : (C.machine.system.histories n hn (leavesEquiv (fan S) _ n flat)).Index)
    (z : Fin ((fan S)^n) × P) :
    let root := state C.machine.system n hn (leavesEquiv (fan S) _ n flat) q
    (root.val.rows.site (root.val.pack.layout.attach ((portEquiv (fan S) P n).symm z))).val =
      flatOffset (compiledOffset S start) n z.1 +
        ((flat z.1).val.rows.site ((flat z.1).val.pack.layout.attach z.2)).val := by
  let read (n : ℕ) (s : Admit n) (p : Port (fan S) P n) := (s.val.rows.site (s.val.pack.layout.attach p)).val
  exact assignedRows_flat C.machine.system (compiledOffset S start) read
    (fun t ht c q i p => compiledEpoch_row (C.atLevel t ht) c q i p) n hn flat q z

/-- The physical row at a repeated bottom input, stated directly on the
actual finite system histogram used by the transcript checker. -/
theorem compiledRepeated_row (bottom : Admit 0) (n : ℕ) (hn : n ≤ T) :
    ∀ q : (C.machine.system.histories n hn (repeatLeaf (fan S) bottom n)).Index, ∀ z : Fin ((fan S)^n) × P,
    let root := state C.machine.system n hn (repeatLeaf (fan S) bottom n) q
    (root.val.rows.site (root.val.pack.layout.attach ((portEquiv (fan S) P n).symm z))).val =
      flatOffset (compiledOffset S start) n z.1 + (bottom.val.rows.site (bottom.val.pack.layout.attach z.2)).val := by
  rw [← flat_repeat bottom n]
  exact compiledFlat_row C n hn (fun _ => bottom)

/-- The same numeric row in the packHistory index used for the physical
tensor and the terminal receiving-site injection. -/
theorem compiledPack_row (bottom : Admit 0) (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom C.machine.epoch n).Index)
    (z : Fin ((fan S)^n) × P) :
    let root := (packHistory bottom C.machine.epoch n).term q
    (root.val.rows.site (root.val.pack.layout.attach ((portEquiv (fan S) P n).symm z))).val =
      flatOffset (compiledOffset S start) n z.1 + (bottom.val.rows.site (bottom.val.pack.layout.attach z.2)).val := by
  let eqv := outerEquiv (T := T) bottom C.machine.epoch n hn
  have hx := compiledRepeated_row C bottom n hn
  rw [C.machine.system_eq] at hx
  have h := outerEquiv_state bottom C.machine.epoch n hn (eqv.symm q)
  change (packHistory bottom C.machine.epoch n).term (eqv (eqv.symm q)) = _ at h
  rw [eqv.apply_symm_apply] at h
  let read (s : Admit n) := (s.val.rows.site (s.val.pack.layout.attach ((portEquiv (fan S) P n).symm z))).val
  exact (congrArg read h).trans (hx (eqv.symm q) z)

section Grid

variable {tiles : ℕ} {portWidth : Fin tiles → ℕ}
variable (compiled : SelectedSchedule.Compiled portWidth deep budget cap w)
variable (bottom : Admissible (Boundary.Good (S := S) (start := start) (bits := portWidth)
  (shape := SelectedSchedule.boundaryShape S start) (w := w) budget) 0)
variable (order : ∀ p : Fin tiles, (bottom.val.rows.site (bottom.val.pack.layout.attach p)).val = p.val)
include order

/-- For the initial tile-indexed port bank, the within-bundle row is the
actual original tile ordinal. -/
theorem compiledRepeated_gridRow (n : ℕ) (hn : n ≤ T)
    (q : (compiled.machine.system.histories n hn (repeatLeaf (fan S) bottom n)).Index)
    (z : Fin ((fan S)^n) × Fin tiles) :
    let root := state compiled.machine.system n hn (repeatLeaf (fan S) bottom n) q
    (root.val.rows.site (root.val.pack.layout.attach ((portEquiv (fan S) (Fin tiles) n).symm z))).val =
      flatOffset (compiledOffset S start) n z.1 + z.2.val := by
  exact (compiledRepeated_row compiled bottom n hn q z).trans (congrArg (_ + ·) (order z.2))

/-- Tile-indexed receiving row on the genuine selected pack history. -/
theorem compiledPack_gridRow (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom compiled.machine.epoch n).Index)
    (z : Fin ((fan S)^n) × Fin tiles) :
    let root := (packHistory bottom compiled.machine.epoch n).term q
    (root.val.rows.site (root.val.pack.layout.attach ((portEquiv (fan S) (Fin tiles) n).symm z))).val =
      flatOffset (compiledOffset S start) n z.1 + z.2.val := by
  exact (compiledPack_row compiled bottom n hn q z).trans (congrArg (_ + ·) (order z.2))

end Grid
end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
