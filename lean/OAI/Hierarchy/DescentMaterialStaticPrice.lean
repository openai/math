import OAI.Hierarchy.DescentMaterialProgram
import OAI.Hierarchy.DescentDatedPriorHeaderInvoice

namespace OAI
/-! # Literal instruction and word counts for the material charts, joins, and receiver maps -/
namespace Hierarchy.DescentDatedAddressBook.MaterialProgram
open DescentSixParty.Chronology DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSharedCableNames DescentHaloPackedRebase DescentHaloWalkRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescentStaticWordColumn
noncomputable section

/-- Include the fixed scan instruction, every literal opcode, and its register and branch names. -/
def wordColumn (n : ℕ) := 4+10*n+7*(15*(n+1))
def phaseCost {w : ℕ} (p : NativePhase w) := p.ticks+7*names p.program
theorem phaseCost_seq {w : ℕ} (a b : NativePhase w) : phaseCost (a.seq b)=phaseCost a+phaseCost b := by
  simp only [phaseCost,NativePhase.seq,names_seq];ring

variable (s : MaterialProgram)
set_option quotPrecheck false
local notation "e" => s.extent
local notation "fmt" => s.depot
local notation "P" => breadth (fmt).degree

def headerPrice (H G M D : ℕ) := PriorHeader.time H G M D+7*PriorHeader.code H G M D

theorem header_fee (H G M D base : ℕ) (adj : Bank) (w : ℕ) :
    phaseCost (PriorHeader.phase H G M D base adj w)≤headerPrice H G M D := by
  obtain ⟨time,hardware⟩:=PriorHeader.priced H G M D base adj w
  exact Nat.add_le_add time (Nat.mul_le_mul_left 7 hardware)

def chartPrice := wordColumn (DonorChartBook.words (e).oldHosts (e).oldGroups (e).oldLanes P)

theorem chart_fee (base w : ℕ) : phaseCost (s.materialCharts base w)=s.chartPrice := by
  simp only [phaseCost,materialCharts,DonorChartBook.install,chartPrice,wordColumn,names_mount]

def joinPrice :=
  let page:=2*2^((DepotRAM.totalBits fmt+DepotRAM.chartBits fmt)*(e).oldLanes)
  let work:=32+40*P
  wordColumn page+(4+(e).sourceRows*(2*work+4))+7*(11+4*work)

theorem join_fee (base : ℕ) (parts reverse : Bank) (w : ℕ) :
    phaseCost (s.materialJoin base parts reverse w)≤ s.joinPrice := by
  let left : Expr:=.lookup parts .row
  let right:=context (s.rankHeader base reverse)
  let work:=(RegisterJoin.expr (DepotRAM.totalBits fmt) (DepotRAM.chartBits fmt) (e).oldLanes
    ((e).joinBase base) left right).work
  have shape:work=left.work+right.work+11:=DescentPackedZip.work ..
  have lhs:left.work≤20:=by simp [left,Expr.work]
  have rhs:right.work≤1+40*P:=context_work _
  have cost:work≤32+40*P:=by omega
  unfold phaseCost materialJoin RegisterJoin.phase joinPrice wordColumn
  simp only [names_seq,DescentOrdinaryAtomFieldRAM.ROM.mount,names_mount,names_scan,RegisterJoin.size]
  change 4+10*_+(4+(e).sourceRows*(2*work+4))+7*(15*(_+1)+(11+4*work))≤_
  have a:=Nat.mul_le_mul_left (e).sourceRows (Nat.add_le_add_right (Nat.mul_le_mul_left 2 cost) 4)
  omega

def mapPrice :=
  let maps:=(e).hosts*chunks (e).groups (e).lanes
  wordColumn (((2*(e).blocks)*2)*2^(((e).fieldBits*(e).blocks+(e).fieldBits)*(e).lanes))+
  wordColumn maps+wordColumn (((e).reach+1)*maps)

theorem map_fee (base w : ℕ) : phaseCost (s.materialMaps base w)=s.mapPrice := by
  unfold materialMaps DepotRAM.Material.Route.Projection.stage
  rw [phaseCost_seq,phaseCost_seq]
  change (4+10*_+7*names (DescentStaticWordColumn.program w _ _ _))+
    (4+10*_+7*names (DescentStaticWordColumn.program w _ _ _))+
    (4+10*_+7*names (DescentStaticWordColumn.program w _ _ _))=_
  simp only [names_mount,wordColumn,mapPrice,DepotRAM.Material.Route.Projection.width]

end
end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
