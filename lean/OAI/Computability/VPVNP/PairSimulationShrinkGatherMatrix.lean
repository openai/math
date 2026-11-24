import OAI.Computability.VPVNP.PairSimulationShrinkGatherImage
import OAI.Computability.VPVNP.PairSimulationMapHandlerFrame

/-!
# Running one selected party gather and its matrix in the same machine

The operand gather reads the selected stage and produces its exact scratch
update. The grouped matrix tests those fields, updates the histogram, and
returns to the row increment. A failed test rules out every returning burst.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.ShrinkSlots
open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifGrid MotifBlocks MotifConversion MapHandlerOperand NodeArguments.ChildScan
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {p r t shared w g endAddr : ℕ} (F : MapHandlerImage.Family B t shared)
  (G : ShrinkGatherBank.Family F) (S : Registers shared) (pc : GatherAddress F G → Fin p)
  (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r)
  (own : F.PrivateReg ↪ Fin r) (gatherReg : G.PrivateReg ↪ Fin r) (temp : Fin r) (ret : Fin p)
  (M : Machine w p r 11) (link : GatherLinked F G S pc dfs saved common own gatherReg temp ret M)
  (mapApart : F.Apart dfs saved common own) (gatherApart : G.Apart dfs saved common gatherReg)
  {X : State G.a (packingLaneBits G.a g)} {δ : ℝ}
  {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} {selection : X.ShrinkSelection B}
  {motif : X.packingData.Motif} (I : LocalHistory.EntryInput B)
  (J : ShrinkPartyNative.Job X B ready selection motif I.party w)
  (hw : MapConstants.widthThreshold B ≤ w)
  (P : Fin 5 → Word w) (st : Word w) (m : Memory w)
  (W : Workspace F demandMass_pos I) (oldScratch : DFS.Scratch w endAddr)

local notation "side" => selectedLayout X B selection
local notation "z" => demandGrid B demandMass_pos I.demand
local notation "key" => (Prod.mk (z) I.party)
local notation "gTrace" => J.trace (G.operands (key)) (G.node (key)) P st m
local notation "post" => J.updated endAddr oldScratch
local notation "raw" => F.action demandMass_pos I hw P st m W endAddr (post)
local notation "ptr" => PhaseRecipe.Expr.eval P st m (F.base (key))
local notation "L" => F.layout (key)

/-- Prepend the selected party's gather trace to a successful matrix action on the
gathered scratch. A rejected matrix entry yields `none`. -/
noncomputable def gatheredAction : Option (List (Event w) × DFS.Scratch w endAddr) :=
  (raw).map fun pair ↦ ((gTrace) ++ pair.1, pair.2)

variable {level absolute : Word w} {T U : IncidenceDirectory w} {origin layer pitch : ℕ}
  {heads : SlotLevel.Heads}

set_option maxHeartbeats 1300000 in
-- The selected term, typed packet and installed register bank have dependent indices.
include link mapApart gatherApart in
/-- The actual installed gather, descriptor writer and selected matrix act on
a typed job and private packets with independent lower stack and scratch words. -/
theorem gathered_native (allowed : ℕ → Prop)
    (sites : ∀ c i, (J.row c i).ReadSafe
      (ShrinkPartyNative.setups (G.operands (key)) (G.node (key)) G.a G.b I.party side c i)
      allowed P st m)
    (old : J.OldPublished (G.operands (key)) P st m level T origin)
    (next : J.SupplyPublished (G.operands (key)) (G.node (key)) P st m heads absolute U layer pitch)
    (c : Config w p r)
    (atGather : c.pc = G.entry (gatherPC F G pc) (writer F G pc) (z) I.party side)
    (inputs : ∀ j : Fin 5, c.reg (F.inputs dfs saved common (key) j.castSucc) = P j)
    (stateReg : c.reg (F.inputs dfs saved common (key) (Fin.last 5)) = st)
    (packets : J.Packets endAddr c.privateMem)
    (incoming : DFS.scratch endAddr c.privateMem = oldScratch)
    (readyCall : ∀ out : Config w p r, J.Assembled c.privateMem out.privateMem →
      MapHandlerOperand.pub F demandMass_pos I dfs saved common out = P →
      MapHandlerOperand.state F demandMass_pos I dfs saved common out = st →
      Prepared F demandMass_pos I dfs saved common out m W)
    (room : Bounds F demandMass_pos I W endAddr (ptr))
    (histBefore : ∀ l : Fin t, ((W.hist + l.val : ℕ) : Word w).val < J.scratch.staging) :
    match gatheredAction F G I J hw P st m W oldScratch with
    | none => ∀ bs, ¬ DFS.Returns M c m bs
    | some (es, updated) => ∃ out, Prefix M m c out [] es ∧
        out.pc = loopPC F (corePC F G pc) true ∧ ShrinkRole.Frame dfs endAddr c out ∧
        (∀ j, out.reg (dfs j) = c.reg (dfs j)) ∧ (∀ j, out.reg (saved j) = c.reg (saved j)) ∧
        (∀ j, out.reg (common j) = c.reg (common j)) ∧
        (∀ q, q.val < J.scratch.staging →
          q.val < (ptr).val ∨ (ptr).val + Fintype.card ShrinkCallFields.Arg ≤ q.val →
          MapCallSetup.Outside (L).core ((L).corePC (L).locations) W q →
          out.privateMem q = c.privateMem q) ∧
        (∀ l : Fin t, out.privateMem ((W.hist + l.val : ℕ) : Word w) =
          c.privateMem ((W.hist + l.val : ℕ) : Word w) +
            (((names F demandMass_pos I).getD []).count l : Word w)) ∧
        DFS.scratch endAddr out.privateMem = updated := by
  obtain ⟨mid, run, assembled, _, upper, lower, dreg, sreg, creg⟩ :=
    G.execute_exact (gatherPC F G pc) dfs saved common gatherReg (writer F G pc) (z) J M
      link.gather gatherApart P st m old next allowed sites c atGather inputs stateReg packets
  have keep (j : Fin 6) : mid.reg (F.inputs dfs saved common (key) j) =
      c.reg (F.inputs dfs saved common (key) j) := by
    unfold MapHandlerImage.Family.inputs
    rcases F.source (key) j with j | j | j
    · exact dreg j
    · exact sreg j
    · exact creg j
  have pEq : MapHandlerOperand.pub F demandMass_pos I dfs saved common mid = P :=
    funext fun j ↦ (keep j.castSucc).trans (inputs j)
  have sEq : MapHandlerOperand.state F demandMass_pos I dfs saved common mid = st :=
    (keep (Fin.last 5)).trans stateReg
  have ptrEq : MapHandlerOperand.addr F demandMass_pos I dfs saved common mid m = (ptr) :=
    (congrArg (fun x ↦ PhaseRecipe.Expr.eval x
      (MapHandlerOperand.state F demandMass_pos I dfs saved common mid) m (F.base (key))) pEq).trans
        (congrArg (fun x ↦ PhaseRecipe.Expr.eval P x m (F.base (key))) sEq)
  have pre : Prefix M m c mid [] (gTrace) := fun fuel more ↦ run.execute fuel more
  have preFrame : ShrinkRole.Frame dfs endAddr c mid := ⟨fun j _ ↦ dreg j, lower, run.persistent⟩
  have postEq : DFS.scratch endAddr mid.privateMem = (post) :=
    upper.trans (congrArg (J.updated endAddr) incoming)
  have mat := Prepared.action_native F demandMass_pos I dfs saved common mid m
    (handlerPC F (corePC F G pc)) own (loopPC F (corePC F G pc) true) M link.matrix mapApart hw
    W endAddr (post) postEq run.pc (readyCall mid assembled pEq sEq) (ptrEq ▸ room)
  rw [pEq, sEq] at mat
  cases h : (raw) with
  | none =>
    rw [h] at mat
    simp only [gatheredAction, h, Option.map_none]
    exact fun bs hret ↦ mat bs ((pre.returns bs).mp hret)
  | some pair =>
    obtain ⟨es, updated⟩ := pair
    rw [h] at mat
    obtain ⟨out, ran, atEnd, frame, df, sf, cf, mem, hist, us⟩ := mat
    simp only [gatheredAction, h, Option.map_some]
    refine ⟨out, pre.trans ran, atEnd, preFrame.trans frame,
      fun j ↦ (df j).trans (dreg j), fun j ↦ (sf j).trans (sreg j),
      fun j ↦ (cf j).trans (creg j), ?_, ?_, us⟩
    · intro q lo exterior outside
      exact (mem q (ptrEq ▸ exterior) outside).trans (assembled.below q lo)
    · intro l
      exact (hist l).trans (congrArg (fun v : Word w ↦ v + _) (assembled.below _ (histBefore l)))

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
