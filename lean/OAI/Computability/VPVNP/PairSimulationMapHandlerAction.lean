import OAI.Computability.VPVNP.PairSimulationMapHandlerImage
import OAI.Computability.VPVNP.PairSimulationMapCallExact
import OAI.Computability.VPVNP.PairSimulationMapWriterClock
import OAI.Computability.VPVNP.PairSimulationMapScratch

/-!
# Deterministic actions of selected grid and party handlers

An action depends on the recorded motif entry, the six descriptor operands,
external memory and the incoming upper scratch. It is defined at exactly the
successful entries. The chronological trace includes the external reads of the
argument writer and all ticks of the initialized and lowered map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapHandlerImage.Family

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry
open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe MapConstants
open private RegisterSetup.no_choices from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open private tick_log from OAI.Computability.VPVNP.PairSimulationMapArgumentWriter

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'} {t shared w : ℕ}
  (F : Family B t shared) (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
  (hw : widthThreshold B ≤ w) (pub : Fin 5 → BurstRAM.Word w) (state : BurstRAM.Word w)
  (m : Memory w)

local notation "idx" => (demandGrid B hp I.demand, I.party)
local notation "L" => F.layout idx
local notation "d" => demandBits src dst I.party I.demandBits
local notation "x" => mapHalf G (fun _ ↦ inputBits) I.supplyBits
local notation "names" => Prod.fst (runEntry B hp I.demand I.payload I.party d x)

/-- The typed field bits fix all map branch lengths, while the six operands
and external memory fix the precise read addresses and returned words. -/
noncomputable def successEvents : List (Event w) :=
  let selected := (selectorRun G (selectorTable B) (selectorCode B) I.payload I.party x).1
  MapArgumentWriter.events (F.base idx) (F.fields idx) pub state m ++
    List.replicate (MapInline.factor L F.ordinal * selected.elim 0 (entryTicks hp I L F.ordinal hw))
      .tick

theorem successEvents_noChoices : choiceBits (F.successEvents hp I hw pub state m) = [] := by
  simp only [successEvents, MapArgumentWriter.events, PrimedInputRAM.Flow.choiceBits_append,
    RegisterSetup.no_choices, (tick_log _).1, List.nil_append]

/-- All external reads in the full visit belong to the descriptor expressions. -/
theorem successEvents_readsFrom (data : ℕ → Prop)
    (baseSafe : (F.base idx).ReadsFrom data pub state m)
    (fieldSafe : ∀ a, (F.field idx a).ReadsFrom data pub state m) :
    SourceTransport.Reads data (F.successEvents hp I hw pub state m) := by
  intro a v h
  rcases List.mem_append.mp h with read | tick
  · exact MapArgumentWriter.events_readsFrom (F.base idx) (F.fields idx) data pub state m
      baseSafe (fun j ↦ fieldSafe ((F.layout idx).args.symm j)) a v read
  · cases List.eq_of_mem_replicate tick

theorem successEvents_noWrites :
    SourceTransport.Writes (fun _ ↦ False) (F.successEvents hp I hw pub state m) := by
  intro a v h
  rcases List.mem_append.mp h with write | tick
  · exact MapArgumentWriter.events_noWrites (F.base idx) (F.fields idx) pub state m a v write
  · cases List.eq_of_mem_replicate tick

variable (X : MapEntry.Program.Workspace
    (MapInline.callProgram (F.layout (demandGrid B hp I.demand, I.party)))
    I.demand I.payload (demandBits src dst I.party I.demandBits)
    (mapHalf G (fun _ ↦ inputBits) I.supplyBits) t w)
  (endAddr : ℕ) (saved : DFS.Scratch w endAddr)

/-- The selected occurrence either rejects or returns its native trace and
complete outgoing scratch to the enclosing map loop. -/
noncomputable def action : Option (List (Event w) × DFS.Scratch w endAddr) :=
  let layout := L
  if (names).isSome then
    some (F.successEvents hp I hw pub state m, MapScratch.upper layout.core layout.args
      (layout.corePC layout.locations) X ((F.base idx).eval pub state m)
      (selectorWord B (fits_of_threshold B hw).2.2.2) F.ordinal endAddr saved)
  else none

theorem action_none_iff : F.action hp I hw pub state m X endAddr saved = none ↔ names = none := by
  cases h : names <;> simp [action, h]

theorem action_isSome :
    (F.action hp I hw pub state m X endAddr saved).isSome = (names).isSome := by
  cases h : names <;> simp [action, h]

/-- A successful action returns precisely the chronological trace and the
prescribed update of the incoming upper scratch. -/
theorem action_some_iff {es : List (Event w)} {updated : DFS.Scratch w endAddr} :
    let layout := L
    F.action hp I hw pub state m X endAddr saved = some (es, updated) ↔
      (names).isSome = true ∧ es = F.successEvents hp I hw pub state m ∧
      updated = MapScratch.upper layout.core layout.args (layout.corePC layout.locations)
        X ((F.base idx).eval pub state m) (selectorWord B (fits_of_threshold B hw).2.2.2)
        F.ordinal endAddr saved := by
  dsimp only
  cases good : (names).isSome
  · simp only [action, good, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and]
  · simp only [action, good, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
    exact and_congr eq_comm eq_comm

theorem action_noChoices {es : List (Event w)} {updated : DFS.Scratch w endAddr}
    (got : F.action hp I hw pub state m X endAddr saved = some (es, updated)) :
    choiceBits es = [] := by
  dsimp only [action] at got
  split at got
  · rw [← (Prod.mk.inj (Option.some.inj got)).1]
    exact F.successEvents_noChoices hp I hw pub state m
  · contradiction

end PairSimulation.MapHandlerImage.Family

end VPVNP
end Computability
end OAI
