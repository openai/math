import OAI.Computability.BorderVNP.PackedSelectedHistoryBoxRoster
import OAI.Computability.BorderVNP.PackedBoxRosterSupport
import OAI.Computability.BorderVNP.PackedTerminalDescriptionPayload
import OAI.Computability.BorderVNP.PackedOriginalBoxResolution

/-! # Exact support of original-factor erasure in the selected physical history

The public roster starts with empty bodies at the bottom. Its differences from
the full mathematical roster can only occur at the terminal retained row of a
genuine original transmission entry. New paid templates and subdivision holes
are independent of this erasure.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited CellSparse EnrichedOuter Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace Shortening.StaticRows
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] (e : PaidIdentity K D m) (S : SiteSchedule e) (start : ℕ)
variable (number : e.Entry → ℕ)

/-- Any changed terminal row has one specific bottom slot and row-major copy
index. Their chronological displacement is the public compiled port offset. -/
theorem historyRoster_difference
    (full erased : Fin (boundaryShape S start 0).sites → List (List Factor))
    (t : ℕ) (r : Fin (boundaryShape S start t).sites)
    (change : historyRoster S start number full t r ≠ historyRoster S start number erased t r) :
    ∃ (child : Fin ((fan S)^t)) (bottom : Fin (boundaryShape S start 0).sites),
      r.val=flatOffset (compiledOffset S start) t child + bottom.val ∧ full bottom≠erased bottom := by
  induction t with
  | zero => exact ⟨0,r,by simp [flatOffset],change⟩
  | succ t ih =>
    let V := fun j => (before S start t j).sites
    let seeds := fun i : Fin S.rounds => seedCount S start t i.val
    let rect := fun i : Fin S.rounds => (rfl : V (i.val+1) = siteCapacity e (S.fanIn*V i.val) (seeds i))
    let fa := BoxRoster.subdivided (s := boundaryShape S start t) (interiors S)
      (historyRoster S start number full t)
    let fb := BoxRoster.subdivided (s := boundaryShape S start t) (interiors S)
      (historyRoster S start number erased t)
    have diff : BoxRoster.steps e number seeds rect fa S.rounds r ≠ BoxRoster.steps e number seeds rect fb S.rounds r := change
    obtain ⟨inner,subrow,atInner,changed⟩ :=
      BoxRoster.steps_difference e number seeds rect fa fb S.rounds le_rfl r diff
    obtain ⟨prev,subval,hdiff⟩ := BoxRoster.subdivided_difference (interiors S)
      (historyRoster S start number full t) (historyRoster S start number erased t) subrow changed
    obtain ⟨old,first,atOld,baseChange⟩ := ih prev hdiff
    refine ⟨copyIndex (fan S) t (inner,old),first,?_,baseChange⟩
    rw [flatOffset_succ,atInner,subval,atOld,Nat.add_assoc]
    rfl

end PackedHistoryCircuit.Normalized.SelectedSchedule

namespace Diagonal.ExternalSew

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited CellSparse PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.EnrichedOuter RowTrace
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
variable {start T w : ℕ} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ start}
variable (dir : Directory.Layout) {pw : Fin dir.sites → ℕ}
variable (compiled : SelectedSchedule.Compiled pw deep budget cap w)
variable (bottom : Admissible (Boundary.Good (S:=S) (start:=start) (shape:=SelectedSchedule.boundaryShape S start)
  (w:=w) (bits:=pw) budget) 0)
variable (count : dir.entries=(fan S)^T*dir.sites) (order : Fin dir.sites ≃ bottom.val.pack.layout.Site)
variable (initial : ∀ i, bottom.val.pack.layout.attach i=order i)
variable (named : ∀ i, (bottom.val.rows.site (order i)).val=i.val)
variable (q : (packHistory bottom compiled.machine.epoch T).Index)

local notation3 "rootState" => ((packHistory bottom compiled.machine.epoch T).term q).val
local notation3 "entry₀" => (originalDescriptionRows compiled.machine bottom q dir count order).trans (rootState).rows.site

include initial named in
/-- The branch-independent roster with all bottom factor bodies erased agrees
with the full roster at every site outside the authentic original-entry injection. -/
theorem erasedRoster_outside (number : e.Entry → ℕ)
    (initialRoster : Fin (SelectedSchedule.boundaryShape S start 0).sites → List (List Factor))
    (bodies : bottom.val.pack.layout.Site → List (List Factor))
    (base : BoxRoster.Realizes bottom.val.rows.site bodies initialRoster)
    (r : Fin (SelectedSchedule.boundaryShape S start T).sites) (notOriginal : r ∉ Set.range (entry₀)) :
    SelectedSchedule.historyRoster S start number (fun _ => []) T r =
      SelectedSchedule.historyRoster S start number initialRoster T r := by
  by_contra neq
  obtain ⟨bundle,bottomRow,located,changed⟩ := SelectedSchedule.historyRoster_difference e S start number
    initialRoster (fun _ => []) T r (Ne.symm neq)
  have live : bottomRow ∈ Set.range bottom.val.rows.site := by
    by_contra absent
    exact changed (base.hole bottomRow absent)
  obtain ⟨v,atV⟩ := live
  let tile := order.symm v
  let j := (finCongr count).symm (finProdFinEquiv (bundle,tile))
  have tileVal : bottomRow.val=tile.val := by
    rw [←atV]
    simpa only [tile,Equiv.apply_symm_apply] using named tile
  have address : flatOffset (compiledOffset S start) T bundle+tile.val = r.val := by rw [tileVal] at located; exact located.symm
  have pos : 0<(SelectedSchedule.boundaryShape S start T).sites := Nat.zero_lt_of_lt r.isLt
  have eqn := PackedHistoryCircuit.TerminalCells.originalDescription_selector dir compiled bottom count order
    initial named q pos j
  have read := PackedHistoryCircuit.TerminalCells.originalPin_value pos (flatOffset (compiledOffset S start) T)
    (bundle,tile) r address
  refine notOriginal ⟨j,?_⟩
  change (rootState).rows.site (originalDescriptionRows compiled.machine bottom q dir count order j) = r
  rw [←eqn]
  simpa only [j,Equiv.apply_symm_apply] using read

/-- Public box directory selected before any private input, histogram, or final
network placement. Each bottom tile gets an opaque delivery key at its static
compiled site number. Every other row carries only its known paid-template bodies. -/
noncomputable def scheduledBoxes (number : e.Entry → ℕ)
    (pos : 0<(SelectedSchedule.boundaryShape S start T).sites)
    (i : Fin (SelectedSchedule.boundaryShape S start T).sites) : List (CellSparse.Packet.Source.Box (Fin dir.entries)) :=
  let fixedRow := fun j : Fin dir.entries => PackedHistoryCircuit.TerminalCells.originalPins pos
    (flatOffset (compiledOffset S start) T) ((finCongr count) j)
  let known := SelectedSchedule.historyRoster S start number (fun _ => []) T
  (Function.partialInv fixedRow i).elim ((known i).map Sum.inl) fun j => [.inr j]

include initial named in
/-- For every selected branch the static opaque box directory is exactly the
typed schedule identified by its authentic retained-original embedding. -/
theorem scheduledBoxes_eq (number : e.Entry → ℕ) (pos : 0<(SelectedSchedule.boundaryShape S start T).sites) :
    scheduledBoxes dir count number pos = CellPacketGeometry.History.originalBoxes (entry₀)
      (SelectedSchedule.historyRoster S start number (fun _ => []) T) := by
  have key : (fun j : Fin dir.entries => PackedHistoryCircuit.TerminalCells.originalPins pos
      (flatOffset (compiledOffset S start) T) ((finCongr count) j)) = (entry₀) := by
    funext j
    exact PackedHistoryCircuit.TerminalCells.originalDescription_selector dir compiled bottom count order
      initial named q pos j
  funext i
  unfold scheduledBoxes CellPacketGeometry.History.originalBoxes
  rw [key]

include initial named in
/-- Resolution of every original input key and public paid table of the actual
terminal machine, using its bottom realization and single original factor table.
The resulting schedule is fixed before its branch index and private factor values. -/
theorem scheduledBoxes_resolved (rows : ∀ t ht, (compiled.machine t ht).F.SiteRows)
    (number : e.Entry → ℕ) (pos : 0<(SelectedSchedule.boundaryShape S start T).sites)
    (base : Site.Programs bottom.val.pack.layout)
    (initialRoster : Fin (SelectedSchedule.boundaryShape S start 0).sites → List (List Factor))
    (real : BoxRoster.Realizes bottom.val.rows.site (fun v => (base v).program.boxes) initialRoster)
    (fs : Fin dir.entries → List Factor)
    (single : ∀ j, (base ((descriptionOrder bottom.val.pack ((fan S)^T) dir.sites dir.entries count order j).2)).program.boxes = [fs j])
    (i : Fin (SelectedSchedule.boundaryShape S start T).sites) :
    (scheduledBoxes dir count number pos i).map (CellSparse.Packet.Source.factors fs) =
      FinalCell.slots (rootState).rows.site
        (fun v => (compiled.machine.terminalPrivatePrograms rows number bottom base q v).program.boxes) i := by
  rw [scheduledBoxes_eq dir compiled bottom count order initial named q number pos]
  apply originalDescription_resolved compiled.machine rows number bottom base q dir count order _
    (SelectedSchedule.historyRoster S start number initialRoster T) fs _ _ single i
  · exact compiled.historyBoxRoster rows number bottom base initialRoster real T le_rfl q
  · exact erasedRoster_outside dir compiled bottom count order initial named q number initialRoster
      (fun v => (base v).program.boxes) real

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
