import OAI.Computability.VPVNP.PairSimulationShrinkGatherRoute
import OAI.Computability.VPVNP.PairSimulationShrinkRowAction
import OAI.Computability.VPVNP.PairSimulationShrinkGatherRegisters

/-!
# One complete resident shrinking-map occurrence

The published row identifies the motif, party and demand-grid value. The
layout read enters the actual selected gather, whose scratch feeds the
descriptor writer and grouped matrix. The resulting action covers both
return to the enclosing row loop and rejection on a malformed local word.
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

private noncomputable local instance scheduledRowBase : DecidableEq X.Base := Classical.decEq _
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
  (W : Workspace F demandMass_pos I) (oldScratch : DFS.Scratch w endAddr)

local notation "st" => rowOrdinalWord (w := w) (a := G.a) (g := g) X side site i

variable {absolute : Word w} {T U : IncidenceDirectory w} {origin layer pitch : ℕ}
  {heads : SlotLevel.Heads}

set_option maxHeartbeats 4000000 in
-- Align the selected row's grid, dependent motif fields and program embeddings.
include link mapApart gatherApart in
theorem row_native (positive : 0 < w) (outside : ∀ b, common b ≠ tmp)
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
    (c : Config w p r) (start : c.pc = inputPC F (corePC F G pc) (.inr 0))
    (cursor : (c.reg ((reg) 2)).val = (src)) (head : c.reg ((reg) 0) = level)
    (base : c.reg ((reg) 4) = term) (stride : c.reg ((reg) 5) = 10) (one : c.reg ((reg) 10) = 1)
    (inputs : ∀ j : Fin 5, c.reg (F.inputs dfs saved common (key) j.castSucc) = P j)
    (packets : J.Packets endAddr c.privateMem)
    (incoming : DFS.scratch endAddr c.privateMem = oldScratch)
    (readyCall : ∀ out : Config w p r, J.Assembled c.privateMem out.privateMem →
      MapHandlerOperand.pub F demandMass_pos I dfs saved common out = P →
      MapHandlerOperand.state F demandMass_pos I dfs saved common out = (st) →
      Prepared F demandMass_pos I dfs saved common out m W)
    (room : Bounds F demandMass_pos I W endAddr (PhaseRecipe.Expr.eval P (st) m (F.base (key))))
    (histBefore : ∀ l : Fin t, ((W.hist + l.val : ℕ) : Word w).val < J.scratch.staging) :
    match rowAction F G X sel site m level term R i I J hw P W oldScratch with
    | none => ∀ bs, ¬ DFS.Returns M c m bs
    | some (es, updated) => ∃ out, Prefix M m c out [] es ∧
        out.pc = loopPC F (corePC F G pc) true ∧ ShrinkRole.Frame dfs endAddr c out ∧
        (∀ j, out.reg (dfs j) = c.reg (dfs j)) ∧
        (∀ j, Protected S common tmp (common j) → out.reg (common j) = c.reg (common j)) ∧
        (∀ q, q.val < J.scratch.staging →
          q.val < (PhaseRecipe.Expr.eval P (st) m (F.base (key))).val ∨
            (PhaseRecipe.Expr.eval P (st) m (F.base (key))).val +
              Fintype.card ShrinkCallFields.Arg ≤ q.val →
          MapCallSetup.Outside (F.layout (key)).core
            ((F.layout (key)).corePC (F.layout (key)).locations) W q →
          out.privateMem q = c.privateMem q) ∧
        (∀ l : Fin t, out.privateMem ((W.hist + l.val : ℕ) : Word w) =
          c.privateMem ((W.hist + l.val : ℕ) : Word w) +
            (((names F demandMass_pos I).getD []).count l : Word w)) ∧
        DFS.scratch endAddr out.privateMem = updated := by
  obtain ⟨mid, pre, entry, ordinalReg, _, frozen, memEq, perEq⟩ :=
    enterGather F G S pc dfs saved common own gatherReg tmp ret M link X sel side site m level term
      R i positive outside c start cursor head base stride one
  have f (q) (hq : Protected S common tmp q) := frozen q hq.1 hq.2.1 hq.2.2
  have frame : ShrinkRole.Frame dfs endAddr c mid :=
    ⟨fun j _ ↦ f _ (dfSafe j), fun q _ ↦ congrFun memEq q, perEq⟩
  have atG : mid.pc = G.entry (gatherPC F G pc) (writer F G pc) (z) I.party
      (selectedLayout X B sel) :=
    entry.trans (congr (congr (congrArg (G.entry (gatherPC F G pc) (writer F G pc)) grid)
      party) layoutChoice)
  have stateReg : mid.reg (F.inputs dfs saved common (key) (Fin.last 5)) = (st) := by
    rw [stateSource]
    apply Fin.ext
    exact ordinalReg.trans (Nat.mod_eq_of_lt (ordinalReg ▸ (mid.reg ((reg) 6)).isLt)).symm
  have middle := gathered_native F G S pc dfs saved common own gatherReg tmp ret M link mapApart
    gatherApart I J hw P (st) m W oldScratch allowed sites old next mid atG
    (fun j ↦ (f _ (pubSafe j)).trans (inputs j)) stateReg (memEq ▸ packets)
    ((congrArg (DFS.scratch endAddr) memEq).trans incoming)
    (fun out staged ↦ readyCall out (memEq ▸ staged)) room histBefore
  cases h : gatheredAction F G I J hw P (st) m W oldScratch with
  | none =>
    rw [h] at middle
    simp only [rowAction, h, Option.map_none]
    exact fun bs returns ↦ middle bs ((pre.returns bs).mp returns)
  | some pair =>
    obtain ⟨es, updated⟩ := pair
    rw [h] at middle
    obtain ⟨out, run, atEnd, mf, df, _, cf, memory, hist, us⟩ := middle
    simp only [rowAction, h, Option.map_some]
    refine ⟨out, pre.trans run, atEnd, frame.trans mf, fun j ↦ (df j).trans (f _ (dfSafe j)),
      fun j safe ↦ (cf j).trans (f _ safe), ?_, ?_, us⟩
    · intro q lo away ext
      exact (memory q lo away ext).trans (congrFun memEq q)
    · intro l
      exact (hist l).trans (congrArg (fun v : Word w ↦ v + _) (congrFun memEq _))

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
