import OAI.Computability.VPVNP.PairSimulationShrinkMapItem
import OAI.Computability.VPVNP.PairSimulationShrinkLayoutBranch

/-!
# The published shrinking map row and its route trace
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion MapResidentRows NodeArguments.ChildScan
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {w a g : ℕ}
  (X : State a (packingLaneBits a g)) (selection : X.ShrinkSelection B)
  (side : Bool) (site : Site X) (m : Memory w) (level term : Word w)

/-- Classical equality on base vertices for indexing the shrinking directory. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Published data shared by every occurrence of the map list at this site. -/
structure MapRowSource where
  /-- First address of the shrinking resident directories. -/
  first : ℕ
  fit : (ShrinkResidentLayout.layout X first).endAddr < 2 ^ w
  rows : Directory X side ((ShrinkResidentLayout.layout X first).params a true w) m
  /-- Base address of the dense width pairs read by the shrinking term worker. -/
  dense : Word w
  /-- Step limit for each burst of the term worker. -/
  cap : ℕ
  /-- Public memory before the term worker ran. -/
  before : Memory w
  /-- Burst reports from writing the selected term records. -/
  reports : List (Report w)
  terms : ShrinkTermSelection.Written B X dense term 10 cap selection before reports
  termFit : term.val + (LocalHistory.shrinkMotifOrder X).length * 10 ≤ 2 ^ w
  retained : ∀ x : X.packingData.Motif, m (term.val + (ordinal X x).val * 10) =
    after before (eventLog reports) (term.val + (ordinal X x).val * 10)
  layout : m (level + 38).val = (side.toNat : Word w)

variable (R : MapRowSource X selection side m level term)
  (i : Fin (order X side site).length)

/-- Address of entry `i` in the site's resident list of map IDs. -/
noncomputable def rowCursor :=
  ((ShrinkResidentLayout.layout X R.first).params a true w 5).val +
    (siteIndex X site).val * capacity a + i.val

/-- Demand grid determined by the shrinking widths of the motif in entry `i`. -/
noncomputable def rowGrid := demandGrid B demandMass_pos
  (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth (entry X side site i).1)

/-- Events for reading the map ID and term, dispatching to the grid and party, and
reading the layout before the gather begins. -/
noncomputable def routeEvents :=
  MapResidentInputs.itemEvents m (rowCursor X selection side site m level term R i : Word w)
    term 10 ++ List.replicate
      (1 + ((2 * ((demandOrder B.grid.demands).symm (rowGrid (B := B) X side site i)).val + 1) +
        (2 * (entry X side site i).2.val + 1))) .tick ++ ShrinkLayoutBranch.events m level


section Header

open MotifBlocks MotifConversion MotifGrid Compression.ShrinkMotif MapResidentInputs

variable {d l p r k : ℕ} {Z : State d (packingLaneBits d l)}
  {factor : ℝ} {F : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {s : Z.ShrinkSelection F} {layout : Bool} {level address : Word w}
  {mem : Memory w} {M : Machine w p r k}

/-- The linked header enters the map guard with exactly the real cursor,
exclusive end, term base and stride of this selected site. -/
theorem MapRowSource.header_native (R : MapRowSource Z s layout mem level address)
    (site : Site Z) (pc : Fin 16 → Fin p) (reg : Fin 11 ↪ Fin r) (done : Fin p)
    (link : HeaderLinked M pc reg done) (c : Config w p r) (entry : c.pc = pc 0)
    (levelReg : c.reg (reg 0) = level) (siteReg : (c.reg (reg 1)).val = (siteIndex Z site).val)
    (words : Published mem level ((ShrinkResidentLayout.layout Z R.first).params d true w 3)
      ((ShrinkResidentLayout.layout Z R.first).params d true w 5) address 10)
    (room : level.val + 37 < 2 ^ w) :
    let baseRow := ((ShrinkResidentLayout.layout Z R.first).params d true w 5).val +
      (siteIndex Z site).val * capacity d
    ∃ out, Prefix M mem c out [] (headerEvents mem level (c.reg (reg 1))) ∧
      HeaderResult reg done mem c out ∧ out.reg (reg 2) = (baseRow : Word w) ∧
      out.reg (reg 3) = ((baseRow + (order Z layout site).length : ℕ) : Word w) ∧
      out.reg (reg 4) = address ∧ out.reg (reg 5) = 10 := by
  obtain ⟨out, run, result⟩ := MapResidentInputs.header_native link mem c entry
  rw [levelReg] at run
  exact ⟨out, run, result, result.directory Z R.first R.fit R.rows site siteReg address
    (levelReg ▸ words) (levelReg ▸ room)⟩

end Header

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
