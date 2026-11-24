import OAI.Computability.VPVNP.PairSimulationShrinkScheduledRow
import OAI.Computability.VPVNP.PairSimulationShrinkLiveOperands
import OAI.Computability.VPVNP.PairShrinkGatherQuiet
import OAI.Computability.VPVNP.PairSimulationResidentMapLoopExact

/-!
# The concrete shrinking-map item of the exact row interpreter
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.ShrinkSlots
open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifGrid MotifBlocks MotifConversion MapResidentRows MapHandlerOperand NodeArguments.ChildScan
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {p r t shared w g endAddr : ℕ} (F : MapHandlerImage.Family B t shared)
  (G : ShrinkGatherBank.Family F) (S : Registers shared) (pc : GatherAddress F G → Fin p)
  (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r)
  (own : F.PrivateReg ↪ Fin r) (gatherReg : G.PrivateReg ↪ Fin r) (tmp : Fin r) (ret : Fin p)
  (M : Machine w p r 11) (link : GatherLinked F G S pc dfs saved common own gatherReg tmp ret M)
  (mapApart : F.Apart dfs saved common own) (gatherApart : G.Apart dfs saved common gatherReg)
  (X : State G.a (packingLaneBits G.a g)) {δ : ℝ}
  {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} (sel : X.ShrinkSelection B)
  (site : Site X) (m : Memory w) (level term : Word w)

private noncomputable local instance scheduledItemBase : DecidableEq X.Base := Classical.decEq _
variable {side : Bool}

variable (R : MapRowSource X sel side m level term) (i : Fin (order X side site).length)
  (I : LocalHistory.EntryInput B)

local notation "entryPair" => MapResidentRows.entry X side site i
local notation "z" => demandGrid B demandMass_pos I.demand
local notation "key" => Prod.mk (z) I.party
local notation "route" => routeEvents X sel side site m level term R i
local notation "src" => rowCursor X sel side site m level term R i
local notation "reg" => S.headerReg common

variable {jobMotif : X.packingData.Motif}
  (J : ShrinkPartyNative.Job (a := G.a) (b := G.b) (g := g) X B ready sel jobMotif I.party w)
  (hw : MapConstants.widthThreshold B ≤ w) (P : Fin 5 → Word w)
  (W : Workspace F demandMass_pos I)

local notation "st" => rowOrdinalWord (w := w) (a := G.a) (g := g) X side site i

variable {absolute : Word w} {T U : IncidenceDirectory w} {origin layer pitch : ℕ}
  {heads : SlotLevel.Heads}

variable (inv : Word w → Config w p r → Prop)

local notation "loopProg" => loop F S (corePC F G pc) common ret
local notation "action" => rowAction (endAddr := endAddr) F G X sel site m level term R i I J hw P W

set_option maxHeartbeats 1900000 in
-- The reader, party fields and local matrix share the actual selected row index.
include link mapApart gatherApart in
theorem exact_item (positive : 0 < w) (outside : ∀ b, common b ≠ tmp)
    (dfSafe : ∀ j, Protected S common tmp (dfs j))
    (pubSafe : ∀ j : Fin 5, Protected S common tmp (F.inputs dfs saved common (key) j.castSucc))
    (stateSource : F.inputs dfs saved common (key) (Fin.last 5) = (reg) 6)
    (layoutChoice : side = selectedLayout X B sel)
    (party : (entryPair).2 = I.party) (grid : rowGrid (B := B) X side site i = (z))
    (allowed : ℕ → Prop) (sites : ∀ c k, (J.row c k).ReadSafe
      (ShrinkPartyNative.setups (G.operands (key)) (G.node (key)) G.a G.b I.party
        (selectedLayout X B sel) c k)
      allowed P (st) m)
    (old : J.OldPublished (G.operands (key)) P (st) m level T origin)
    (next : J.SupplyPublished (G.operands (key)) (G.node (key)) P (st) m heads
      absolute U layer pitch)
    (room : Bounds F demandMass_pos I W endAddr (PhaseRecipe.Expr.eval P (st) m (F.base (key))))
    (histBefore : ∀ l : Fin t, ((W.hist + l.val : ℕ) : Word w).val < J.scratch.staging)
    (live : ∀ n c, inv n c → LiveOperands (endAddr := endAddr) F S dfs saved common tmp
      I J P (st) m level term W inv n c) :
    ResidentMapLoop.Exact.Item (endAddr := endAddr) (loopProg) M m dfs inv (src)
      (fun _ saved ↦ (action) saved) := by
  have clock (n : Word w) (c : Config w p r) (entryPC : c.pc = (loopProg).item)
      (atSrc : c.reg (loopProg).cursor = ((src) : Word w)) (hin : inv n c) :=
    let h := live n c hin
    row_native F G S pc dfs saved common own gatherReg tmp ret M link mapApart gatherApart X sel
      site m level term R i I J hw P W (DFS.scratch endAddr c.privateMem) positive outside dfSafe
      pubSafe stateSource layoutChoice party grid allowed sites old next c entryPC
      ((congrArg Fin.val atSrc).trans
        (Nat.mod_eq_of_lt (rowCursor_fit X sel side site m level term R i)))
      h.head h.base h.stride h.one h.pubWords h.packets rfl h.prepare room histBefore
  have safe (l : Fin 11) (lo : l.val < 6 ∨ 9 < l.val) : Protected S common tmp ((reg) l) := by
    refine ⟨outside _, common.injective.ne (S.apart l).symm, ?_⟩
    intro j a b
    exact (reg).injective.ne (by intro eqn; rw [eqn] at lo; omega)
  constructor
  · intro node oldScratch es updated got
    exact rowAction_noChoices F G X sel site m level term R i I J hw P W oldScratch
      (J.trace_noChoices (G.operands (key)) (G.node (key)) P (st) m) got
  · intro node c es updated enter cursor hin got
    have run := clock node c enter cursor hin
    change (action) (DFS.scratch endAddr c.privateMem) = some (es, updated) at got
    rw [got] at run
    obtain ⟨out, path, advance, frame, _, kept, memory, _, upper⟩ := run
    exact ⟨out, advance, (live node c hin).preserve out kept memory,
      kept _ (safe 2 (by decide)), kept _ (safe 3 (by decide)), kept _ (safe 10 (by decide)),
      frame, upper, path⟩
  · intro node c enter cursor hin got
    have run := clock node c enter cursor hin
    change (action) (DFS.scratch endAddr c.privateMem) = none at got
    rw [got] at run
    exact run

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
