import OAI.Computability.VPVNP.PairSimulationShrinkGatherRegisters
import OAI.Computability.VPVNP.PairSimulationMapHandlerOperand

/-!
# Operands carried through a shrinking-map list
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion MapHandlerOperand
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {p r t shared w a b g endAddr : ℕ} (F : MapHandlerImage.Family B t shared)
  (S : Registers shared) (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
  (common : Fin shared ↪ Fin r) (tmp : Fin r)
  {X : State a (packingLaneBits a g)} {δ : ℝ}
  {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection B}
  {motif : X.packingData.Motif} (I : LocalHistory.EntryInput B)
  (J : ShrinkPartyNative.Job X B ready sel motif I.party w)
  (P : Fin 5 → Word w) (st : Word w) (m : Memory w) (level term : Word w)
  (W : Workspace F demandMass_pos I) (inv : Word w → Config w p r → Prop)

local notation "reg" => S.headerReg common
local notation "key" => Prod.mk (demandGrid B demandMass_pos I.demand) I.party

/-- Live words and protected packet geometry after the child and absorbed-bit scans. -/
structure LiveOperands (node : Word w) (c : Config w p r) : Prop where
  head : c.reg ((reg) 0) = level
  base : c.reg ((reg) 4) = term
  stride : c.reg ((reg) 5) = 10
  one : c.reg ((reg) 10) = 1
  pubWords : ∀ j : Fin 5, c.reg (F.inputs dfs saved common (key) j.castSucc) = P j
  packets : J.Packets endAddr c.privateMem
  prepare : ∀ out : Config w p r, J.Assembled c.privateMem out.privateMem →
    MapHandlerOperand.pub F demandMass_pos I dfs saved common out = P →
    MapHandlerOperand.state F demandMass_pos I dfs saved common out = st →
    Prepared F demandMass_pos I dfs saved common out m W
  preserve : ∀ out : Config w p r, (∀ j, Protected S common tmp (common j) →
    out.reg (common j) = c.reg (common j)) →
    (∀ q, q.val < J.scratch.staging →
      q.val < (PhaseRecipe.Expr.eval P st m (F.base (key))).val ∨
        (PhaseRecipe.Expr.eval P st m (F.base (key))).val +
          Fintype.card ShrinkCallFields.Arg ≤ q.val →
      MapCallSetup.Outside (F.layout (key)).core ((F.layout (key)).corePC
        (F.layout (key)).locations) W q → out.privateMem q = c.privateMem q) → inv node out

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
