import OAI.Hierarchy.GridChosenReceiverSlotScale
import OAI.Hierarchy.GridChosenReceiverDescendants

namespace OAI
/-! # Returning the selected receiver's priced terminal maps -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal Diagonal.HistoryContraction Diagonal.PhysicalStage
open RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution GridScale GridThrough
open GridRegisteredSetting GridInstalledEvaluator Filter
open TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {B : Block F} {m A w : ℕ}
variable {Q : ℕ→ℕ} {loss : ℕ→ℝ} {v : TickSelection F (m+1) A w Q loss}
variable (I : Installed B m A w (degree B) (stageRate B) rootRate v)
variable (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I reserve 0)
set_option quotPrecheck false
local notation "D" => I.D
local notation "l" => layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate
local notation "n" => (l).sideMinusOne
local notation "channels" => GridControllerSimGeometry.railCount m n (l).bank
local notation "W" => (64*w)
local notation "gate" => (26*GridDescription.sector w)
local notation "arch" => GridDescription.capacity w
local notation "p" => (l).pinWidth
local notation "clock" => UniversalTick.clock w UniversalTick.saving
local notation "H" => (clock/40000)
local notation "V" => TraceAdmission.receiverAge w
local notation "units" => (D).issuedUnit w (degree B) (stageRate B) rootRate
local notation "widths" => (fun i=>(v.replacement.width_le_size i).trans v.size_le)
local notation "U" => TraceReceiverSeedWords.wordsLayout (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "trees" => TraceReceiverSeedWords.forest (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "work" z:arg => (D).work z.1 (D).issuedCharges units
local notation "cost" z:arg => (D).costs (GridNativeImage.resources D l) z.1 m n (l).bank (D).issuedCharges units
local notation "group" z:arg c:arg j:arg => FactorAllocation.factors w (cost z) (List.ofFn id) (GridTicks.index (c,j))
local notation "chosen" z:arg => (D).run.plan.assemble z.1 ((receiverAssembly I) U) trees
local notation "which" z:arg => ((D).ordinal z.1).symm
local notation "fixed" z:arg => (D).run.terminalLabels z.1 z.2
local notation "table" safe:arg => (GridNativeDispatch.actualTable D safe).codes
local notation "room" safe:arg => GridNativeDispatch.selectorRoom D l R.table R.selector safe
local notation "rooms" recv:arg => (R.rooms recv 0 gate).choose
local notation "input" recv:arg safe:arg z:arg x:arg c:arg j:arg => streamInput I recv 0 gate R.text (rooms recv) widths
  (table safe) (room safe) z x c j
local notation "salt" recv:arg x:arg => (fun i : Fin I.inputSize=>GridDescription.input (x ∘ Wiring.railPin.symm)
  (GridDescription.code (q:=w^2) recv (D).machine) (GridNativeDispatch.source D l v.replacement 0 gate) i.val)

/-- The final root, map, command and cursor instructions on this particular
receiver. Their input is the typed cache from the exact installed descendant
program, and their output is traversed by the installed field evaluator. -/
def InstalledTerminal (geom : GridReceiverDirectory.ElectionRoom D l) : Prop :=
  ∀ (recv : Machine W arch arch arch) (safe : GridNativeDispatch.WordRoom D)
    (z : (D).trace) (x : GridDiagonal.Pins (Fin channels)) (c : Cell (m+1) n) (j : Fin v.copies),
    let t:=GridTicks.index (c,j)
    let ids:=selectedRoots D l z.1 t
    let tape:=input recv safe z x c j
    let sel:=GridReceiverDirectory.InputWindow D l z safe (room safe)
    let elected:=GridReceiverDirectory.Elected D l geom safe z sel t
      (GridReceiverDirectory.shifted l w tape) (GridReceiverDirectory.original D l sel tape)
    let nets:=fun i : Fin ids.length=>((D).issuedTree z.1 ids[i]).compile
    let wire:=slotWire I R geom recv safe z c j
    let spans:=List.ofFn (Gather.rootSpan (TickWorkspace.base V 9) (fun i=>(nets i).cells))
    ∀ before after,elected before → slotCache I R geom recv safe z x c j before after →
      (terminal D l).Spec (·=after) (fun _ out=>
        Gather.Prepared nets (ctrl:=GridReceiverBanks.cursor w) (control:=TickWorkspace.base V 18)
          (atCmd:=GridReceiverBanks.commands w) («H»:=H) wire (fun i:Fin p=>tape i.val)
          (TickWorkspace.base V 9) spans out) (termAllowance D l z.1 ids)

/-- For each sufficiently large aligned machine the native cache replay and
the executable price bound supply the other two phases of the receiver. -/
theorem eventual_local_of_terminal (B : Block F) (m A : ℕ) (env : Envelopes Q loss)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop,∀ age : ℕ,64*w=16*age^10 → Even w →
      ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
      ∀ (I : Installed B m A w (degree B) (stageRate B) rootRate v)
        (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I reserve 0)
        (geom : GridReceiverDirectory.ElectionRoom I.D
          (layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate)),
        InstalledTerminal I R geom → LocalPhases I R geom := by
  filter_upwards [eventual_installed_descendants B env m A q range,eventual_slot_spending B m A env q range]
    with w stored charged
  intro age aligned even v copies I R geom done recv safe z x c j
  let chosenLayout := layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate
  let tick:=GridTicks.index (c,j)
  let ids:=selectedRoots I.D chosenLayout z.1 tick
  exact ⟨TraceReceiverElectedCache.replay I.D chosenLayout z tick,termAllowance I.D chosenLayout z.1 ids,
    slotCache I R geom recv safe z x c j,charged v copies I z tick,
    stored age aligned even v copies I R geom recv safe z x c j,
    done recv safe z x c j⟩

/-- The remaining semantic condition concerns the actual terminal procedure on
the post-replay cache. All its public control parameters have already been
chosen on the same word size and evaluator. -/
theorem receives_of_terminal (B : Block F) (m : ℕ)
    (finish : ∀ A>UniversalTick.saving+2+51,∀ Q loss,
      Envelopes Q loss → ∀ q : ℕ→ℕ,(∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) →
        ∀ᶠ w : ℕ in atTop,∀ age : ℕ,5120≤age → 64*w=16*age^10 → Even w →
          ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
          ∀ (I : Installed B m A w (degree B) (stageRate B) rootRate v)
            (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I reserve 0)
            (geom : GridReceiverDirectory.ElectionRoom I.D
              (layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate)),
            InstalledTerminal I R geom) : Receives B m := by
  apply receives_of_local B m 0
  intro A large Q loss env q valid
  have bound : UniversalTick.saving+2+51<A := by omega
  filter_upwards [eventual_local_of_terminal B m A env q valid,finish A bound Q loss env q valid]
    with w combine maps
  intro age mature aligned even v copies I R geom
  exact combine age aligned even v copies I R geom (maps age mature aligned even v copies I R geom)

end Hierarchy.GridChosenReceiver
end

end OAI
