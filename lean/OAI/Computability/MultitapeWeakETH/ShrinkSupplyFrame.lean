import OAI.Computability.MultitapeWeakETH.ShrinkDemandAddress
import OAI.Computability.VPVNP.PairShrinkCanonicalJob
import OAI.Computability.VPVNP.PairShrinkSurvivingSelected

/-! # Subdivision records for the surviving supply at a selected map -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open VPVNP BurstRAM BurstRAM.PrivateRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments CompressorRecords
open DescriptorSpace PhaseRecipe ShrinkBlockInputs MapResidentRows ShrinkSlots ShrinkSliceSweep
open scoped Classical Fin.CommRing
noncomputable section

/-- The current output packet is read at node zero of its own argument tape. -/
def supplyHeader (a : ℕ) := ShrinkSurvivingSelected.inputs a .state (ordinal a) (.lit 0) packetStride (.lit 0) (.lit 0)

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
  (sel : SelectedScore.Selection B X) (base : Word w) (positions blocks n cur : ℕ) (mem : Memory w)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "old" => levelStart L cur
local notation "next" => levelStart L (cur+1)
local notation "tab" => tableBase L cur
local notation "side" => SelectedFinish.chosen B X sel
local notation "term" => ShrinkInput.termHead (w:=w) X (tab (0 : Fin 6))
local notation "shape" => levelShape (b:=b i) X
local notation "sub" => SlotLevel.Shape.subdivisions shape
local notation "heads" => ShrinkOutput.heads shape (SelectedArena.roleBase X term (10 : Word w)) (tab (3 : Fin 6))
local notation "inc" => packedIncidence L w (cur+1) (actualCount shape)
local notation "absolute" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X (tab (0 : Fin 6))) w
local notation "alloc" => selectedAllocation B.shrink X sel term 10 (tab (2 : Fin 6)) sub
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "slots" => X.shrinkStateIndex (S.shrink i) side
local notation "widths" => branchWidth X B.shrink sel
local notation "arena" => Arena.mk 0 (2*n*n)

set_option maxHeartbeats 1500000 in
/-- Each reverse-copy frame for the parent's subdivision is read from the
selected pass's actual interval, inverse slot, and successor-incidence tables. -/
theorem supply_recorded (stored : CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem)
    (v : Site X) (j : Fin (order X side v).length) (p : Fin 5 → Word w)
    (owner : p 0 = ((siteIndex X v).val : Word w)) (index : p 1 = (j.val : Word w))
    (t : Fin 4) (dir : Bool) (piece : Fin (sub t)) :
    let m := rowMotif X side v j
    let u := ShrinkSurvivingOperands.site X side m t dir
    ∀ z : (Y).network.Half u,
      (ShrinkSurvivingColumn.row X side sub widths slots m t dir z arena 0 0
        (Allocation.row alloc (ShrinkMotifOrder.stateNumber X m,t)) piece).Recorded
        ((supplyHeader (a i)).setup (2^(b i)) sub t dir piece) p (old : Word w) mem := by
  intro m u z
  let H := supplyHeader (a i)
  let layer := (mem (next + 14)).val
  let pitch := (mem (next + 15)).val
  let geom := ShrinkCanonicalJob.geometry B i X (S.shrink i) sel m base positions blocks cur stored.bounds
  have room := stored.words.oldRoom
  have newer := stored.words.nextRoom
  have atOld (j : ℕ) (small : j ≤ 65) : (((old : Word w) + (j : Word w))).val = old+j := by
    rw [← Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have lanes := stored.words.level.residual
  change mem (((old : Word w) + ((3 : ℕ) : Word w)).val) = _ at lanes
  rw [atOld _ (by decide)] at lanes
  have vertices := stored.words.level.vertices
  change mem (((old : Word w) + ((0 : ℕ) : Word w)).val) = _ at vertices
  rw [atOld _ (by decide)] at vertices
  have id := (item_read B i X sel base positions blocks n cur mem stored v j p owner index).1
  have h := ShrinkSurvivingSelected.inputs_readback X m heads absolute old next
    (Allocation.widthEnd alloc) inc arena layer pitch .state (ordinal (a i)) (.lit 0) packetStride (.lit 0) (.lit 0)
    (pub:=p) (state:=(old : Word w)) rfl id rfl
    (packetStride_eval B i X sel base positions blocks n cur mem stored p)
    (by omega) (by omega) vertices ((congrArg Fin.val lanes).trans (Fin.val_cast_of_lt geom.lanes))
    stored.words.supply.absolute stored.words.supply.successor stored.words.supply.inverse stored.words.supply.interval
    (Fin.cast_val_eq_self _).symm (Fin.cast_val_eq_self _).symm
    (stored.words.successor.incidence (3 : Fin 6)) (stored.words.successor.incidence (4 : Fin 6))
    (stored.words.successor.incidence (5 : Fin 6))
  apply ShrinkSurvivingSelected.recorded X (S.shrink i) m t dir piece B.shrink sel term 10
    (tab (2 : Fin 6)) H heads absolute inc arena 0 0 layer pitch z h.1 stored.sources.absolute
    stored.sources.sorted geom.absolute geom.slot geom.degree geom.two geom.allocation _ h.2.1
    stored.sources.successor geom.capacity rfl rfl h.2.2
  intro id
  have image := stored.sources.slices.intervals id
  rw [geom.split_eq] at image
  exact image

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
