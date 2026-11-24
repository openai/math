import OAI.Computability.VPVNP.PairSimulationMapResidentRows
import OAI.Computability.VPVNP.CompressorShrinkScheduledRetention

/-!
# Agreement of the selected and retained shrinking grid words

The native term worker and the later table readback identify the same demand
grid point for every resident motif. The fixed grid enumerates each point
once, so the actual word indices agree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords DescriptorSpace PhaseRecipe Schedule
open Compression BlockPlanner MapResidentRows NodeArguments.ChildScan
open scoped Fin.CommRing

variable {w : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
  (B : S.Templates) (i : Fin S.steps) {g : ℕ}
  (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
  (sel : X.ShrinkSelection B.shrink)
  (base : Word w) (positions blocks round : ℕ) (m : Memory w)

/-- Classical equality decision for base vertices used to compare retained term grid words with
the words written by the term-selection worker. -/
noncomputable local instance termReadbackBaseDecEq : DecidableEq X.Base := Classical.decEq _

local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "first" => Script.levelsPerBlock prog * round
local notation "old" => first + i.val
local notation "tab" => tableBase L old
local notation "term" => ShrinkInput.termHead (w := w) X (tab (0 : Fin 6))
private theorem grid_word_eq {α : Type*} {grid : Finset α} {x : α} {u v : Word w}
    (h : grid.toList[u.val]? = some x) (h' : grid.toList[v.val]? = some x) : u = v := by
  obtain ⟨hu, eu⟩ := List.getElem?_eq_some_iff.mp h
  obtain ⟨hv, ev⟩ := List.getElem?_eq_some_iff.mp h'
  exact Fin.ext (grid.nodup_toList.getElem_inj_iff.mp (eu.trans ev.symm))

/-- The retained grid word equals the one selected by the native term worker. -/
theorem term_readback {T : IncidenceDirectory w} {dense : Word w} {fuel : ℕ}
    {before : Memory w} {rs : List (Report w)}
    (back : ShrinkOutput.ScheduledReadbacks B i X sel base positions blocks round T m)
    (terms : ShrinkTermSelection.Written B.shrink X dense term 10 fuel sel before rs)
    (ten : (10 : Word w).val = 10)
    (fit : (term).val + (LocalHistory.shrinkMotifOrder X).length * 10 < 2 ^ w)
    (e : X.packingData.Motif) :
    m ((term).val + (ordinal X e).val * 10) =
      after before (eventLog rs) ((term).val + (ordinal X e).val * 10) := by
  let id := ShrinkMotifOrder.stateNumber X e
  have grid := (back.resident.terms id).1
  change B.shrink.grid.demands.toList[(m (((term).val + id.val * (10 : Word w).val)
    % (2 ^ w))).val]? = _ at grid
  have index : (ordinal X e).val = id.val := rfl
  have hi : id.val < (LocalHistory.shrinkMotifOrder X).length := index ▸ (ordinal X e).isLt
  have room : (term).val + id.val * 10 < 2 ^ w := by omega
  have eqn : (ShrinkMotifOrder.stateNumber X).symm id = e := Equiv.symm_apply_apply ..
  rw [ten, Nat.mod_eq_of_lt room] at grid
  change _ = some (MotifConversion.demandGrid B.shrink Compression.ShrinkMotif.demandMass_pos
    (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth
      ((ShrinkMotifOrder.stateNumber X).symm id))).val at grid
  rw [eqn] at grid
  have source := (terms.fields e).1
  have address : (ShrinkTermSelection.rowBase X term 10 e).val = (term).val + id.val * 10 :=
    Nat.mod_eq_of_lt room
  rw [address] at source
  rw [index]
  exact grid_word_eq grid source

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
