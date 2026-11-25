import OAI.ThreeFlat.RAM.HistoryRefreshBatch
import OAI.ThreeFlat.RAM.HistoryStageBoundedResources
import OAI.ThreeFlat.Diagonal.HistoryPortFootprint

namespace OAI
/-! # Fixed rates for motif joins and physical block pages -/

namespace ThreeFlat.RAM.HistoryMotifJoin

open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical HistoryBoundedBody HistoryJoinScan
open Diagonal.HistoryContraction PhysicalProcedure
open scoped BigOperators Classical
noncomputable section

def joinCap (B : HistoryGatherBody.Layout) (g : Bool) := if g then B.party.parties else B.party.motifs

def joinRate (B : HistoryGatherBody.Layout) (g : Bool) :=
  let cap:=joinCap B g
  4+(7+7*cap)*(2*(joinHeader B 1 g).binds+4)+100*(1+joinResources cap)*(5+2*cap)

def motifBoot (B : HistoryGatherBody.Layout) := 4+9*(2*(privateHeader B 1).binds+4)

def motifRate (B : HistoryGatherBody.Layout) (pair gather : ℕ) :=
  motifBoot B+B.party.parties*(pair+gather)+joinRate B true

def kernelRate (B : HistoryGatherBody.Layout) (oldCap pair gather : ℕ) :=
  HistoryNodePorts.phaseCost oldCap+(B.party.motifs+1)*motifRate B pair gather+joinRate B false

end
end ThreeFlat.RAM.HistoryMotifJoin

namespace ThreeFlat.RAM.HistoryStageBody.Physical

open HistoryMotifJoin HistoryGatherExecution HistoryRefreshEmitter Diagonal.PhysicalStage
open scoped Classical
noncomputable section

/-- A published grid row fixes the alphabet, coded selector, port count, and digit widths. -/
def partyRate {F : Type} (p : Party F) := partyTariff p.letters p.supplies p.codeBits p.header p.maxDigit

def partyMapRate {F : Type} (B : HistoryGatherBody.Layout) (p : Party F) :=
  schemaCost B*(1+p.port.digits+p.supplies*(p.maxDigit+p.codeBits)+p.supplies*p.codeBits+p.header+p.supplies*p.maxDigit)

def kernelTemplate {F : Type} (G : Grid F) := layout 0 ⟨0,0,0,0,0,0⟩ (G.family 0)

def gridPairRate {F : Type} (G : Grid F) := partyTariff 0 0 0 0 0+(G.rows.map partyRate).sum

def gridMapRate {F : Type} (G : Grid F) :=
  schemaCost (kernelTemplate G)+(G.rows.map (partyMapRate (kernelTemplate G))).sum

def gridKernelRate {F : Type} (G : Grid F) :=
  kernelRate (kernelTemplate G) G.childBound (gridPairRate G) (gridMapRate G)

noncomputable def blockKernelRate {F : Type} [Field F] [Fintype F] (B : Block F) :=
  1+((grids B).map gridKernelRate).sum

private theorem term_le_sum {α : Type*} (xs : List α) (f : α→ℕ) (x : α) (mem : x∈xs) : f x≤(xs.map f).sum := by
  induction xs with
  | nil => simp at mem
  | cons a rest ih =>
    rcases List.mem_cons.mp mem with rfl|inRest
    · exact Nat.le_add_right _ _
    · exact (ih inRest).trans (Nat.le_add_left _ _)

end

end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree
open Diagonal.HistogramTileNetwork Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms
open Diagonal.MotifSelectorChecks LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] [Fintype F]

/-- A fixed coefficient for every local array used by one elected tile. The
last term prices the actual padded native compactor at this tile's digit width. -/
def partyPageRate (ar : ℕ) (p : Party F) :=
  (∑ i : Fin 7,(p.kind ar).words i)+8*partyCoefficient p.header p.codeBits p.letters p.supplies p.maxDigit+
  partyPinCoefficient p.header p.codeBits p.letters p.supplies p.maxDigit+
  23*(5+p.letters+p.supplies)+800000*(p.maxDigit+1)

/-- The permanent port catalogue also stores the physical edge numbers and base widths. -/
def gridPortWords (g : Grid F) :=
  (g.rows.map (fun p=>∑ i : Fin g.stride,p.port.at g.demand g.supply i.val)).sum

def gridPageRate (ar : ℕ) (g : Grid F) :=
  (3+5*g.demand+4*g.supply)+(g.motifs+2)*(g.parties+2)*8*32+gridPortWords g+
    (g.rows.map (partyPageRate ar)).sum

/-- A common fixed storage coefficient for every level of the public program. -/
def blockPageRate (B : Block F) :=
  Fintype.card ((Fin 3→Bool)→F)+((grids B).map (gridPageRate (arity B))).sum

theorem grid_page_rate_le_block (B : Block F) {g : Grid F} (placed : g∈grids B) :
    gridPageRate (arity B) g≤blockPageRate B :=
  (term_le_sum (grids B) (gridPageRate (arity B)) g placed).trans (Nat.le_add_left _ _)

end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
