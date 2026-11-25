import OAI.Computability.BorderVNP.PackedOriginalDescriptionRows
import OAI.Computability.BorderVNP.DiagonalEnrichedOriginalRowOuter
import OAI.Computability.BorderVNP.PackedTerminalRoutingFields

/-! # Compiled private selectors charge the payload of the actual retained box

The row used by the delivery directory and the original-site injection
used by the physical record bound agree on each complete packing history.
Its original description length is consequently paid at the same receiving
vertex that the native placement program reads.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Crossing Cover Shortening Shortening.Adaptive Shortening.PublicCapacity Packing
open BorderVNP.Epoch BorderVNP.Epoch.Round Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open Normalized EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e}
    {start T w : ℕ} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    (dir : Directory.Layout) {pw : Fin dir.sites → ℕ}
    (compiled : SelectedSchedule.Compiled pw deep budget cap w)
    (bottom : Admissible (Boundary.Good (S:=S) (start:=start) (shape:=SelectedSchedule.boundaryShape S start)
      (w:=w) (bits:=pw) budget) 0)
    (count : dir.entries=(fan S)^T*dir.sites) (order : Fin dir.sites ≃ bottom.val.pack.layout.Site)
    (initial : ∀ i, bottom.val.pack.layout.attach i = order i)
    (named : ∀ i, (bottom.val.rows.site (order i)).val = i.val)
    (q : (packHistory bottom compiled.machine.epoch T).Index)

local notation "sh" => SelectedSchedule.boundaryShape S start T
local notation "off" => flatOffset (compiledOffset S start) T

include initial named in
/-- The checked public slot for each original private description equals
the true stable site number of the physical retained-box injection. -/
theorem originalDescription_selector (positive : 0<(sh).sites) (j : Fin dir.entries) :
    let s := ((packHistory bottom compiled.machine.epoch T).term q).val
    let old := originalDescriptionRows compiled.machine bottom q dir count order
    originalPins positive off ((finCongr count) j) = s.rows.site (old j) := by
  intro s old
  let z : Fin ((fan S)^T) × Fin dir.sites := finProdFinEquiv.symm ((finCongr count) j)
  let h := enrichedOuterHosts compiled.machine bottom q
  have id : s.rows.site ((flattenPack T s.pack).layout.attach z) = s.rows.site (old j) :=
    congrArg s.rows.site ((h.attach z).trans (congrArg (fun v => h.site ⟨z.1,v⟩) (initial z.2)))
  have row := compiledPack_gridRow compiled bottom (fun i => (congrArg (fun v => (bottom.val.rows.site v).val) (initial i)).trans (named i))
    T le_rfl q z
  have oi := originalPin_value positive off z _ row.symm
  rw [show finProdFinEquiv z = (finCongr count) j from finProdFinEquiv.apply_symm_apply _] at oi
  exact oi.trans id

include initial named in
/-- The native selector's identified receiver carries the charged original
description. This combines the schedule's true numeric lookup with the
preserved scalar fields of the same physical packing history. -/
theorem originalDescription_charged (positive : 0<(sh).sites) (base : RecordData bottom.val.pack.layout)
    (room : ∀ v, dir.description ≤ base.payload v) :
    let s := ((packHistory bottom compiled.machine.epoch T).term q).val
    let old := originalDescriptionRows compiled.machine bottom q dir count order
    (∀ j, originalPins positive off ((finCongr count) j) = s.rows.site (old j)) ∧
    ∀ j, dir.description ≤ (compiled.machine.historyFields bottom base T q).payload (old j) :=
  ⟨originalDescription_selector dir compiled bottom count order initial named q positive,
   originalDescriptionRows_payload compiled.machine bottom q dir count order base room⟩

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI
