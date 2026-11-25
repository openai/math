import OAI.Hierarchy.DescentMaterialTariffNumbers
import OAI.Hierarchy.DescentMaterialStaticPrice
import OAI.Hierarchy.DescentMaterialSheetsPrice
import OAI.Hierarchy.DescentSignedFeedPrefix

namespace OAI
/-! # Bound each physical setup by literal words and packed old or new rows -/
namespace Hierarchy.DescentDatedAddressBook.MaterialProgram
open DescentSixParty.Chronology DescentRawCablePanel DescentSIMDLookup DescentHaloWalkRAM DescentDyadicSpan
open DescentDatedAddressBook.SignedExtent.FeedBound

private theorem tableCost {n c R : ℕ} (one : 1≤R) (table : Covers R c n) :
    Covers R (4+10*c+7*(15*(c+1))) (wordColumn n) :=
  add (add (constant one 4) (left 10 table)) (left 7 (left 15 (add table (constant one 1))))

theorem prior_rows {H G M D R : ℕ} (live : 1≤R) (hosts : Covers R 1 H)
    (rows : Covers R 1 (H*chunks G M)) :
    Covers R (priorFactor D) (headerPrice H G M D) := by
  let P:=breadth D
  have many:=right hosts (P*P)
  have padRows : Covers R (strideFactor D) (PriorHeader.stride H G M D) := by
    simpa only [P,PriorHeader.stride,strideFactor,Nat.one_mul] using pad live (add (add (add (constant live 1) hosts) many) rows)
  have hdr:=left (P+13) padRows
  have per:=right many (2*PriorHeader.opLimit D+4)
  have clock:=add (add (add (constant live 4) (left 10 hdr)) (left 7 (add (constant live 8) per))) (constant live 4)
  have text:=add (add (left 15 (add hdr (constant live 1)))
    (left 7 (constant live (15+(11+4*PriorHeader.opLimit D))))) (constant live 15)
  simpa only [headerPrice,PriorHeader.time,PriorHeader.code,priorFactor,P,Nat.one_mul] using add clock (left 7 text)

variable (q : MaterialProgram)
set_option quotPrecheck false
local notation "e" => q.extent
local notation "fmt" => q.depot
local notation "P" => breadth (fmt).degree

theorem chart_rows {R : ℕ} (one : 1≤R) (rows : Covers R 1 (e).sourceRows) (lanes : Covers R 1 (e).oldLanes) :
    Covers R (chartFactor (fmt).degree) q.chartPrice := by
  have extent:=add rows (add rows (left P (right (add lanes (constant one 1)) (P+1))))
  simpa only [MaterialExtent.sourceRows,chartFactor,chartPrice,DonorChartBook.words,DonorChartBook.pages,Nat.mul_one,Nat.one_mul] using tableCost one extent

theorem join_rows {R : ℕ} (one : 1≤R) (rows : Covers R 1 (e).sourceRows)
    (page : Covers R 1 (2^((DepotRAM.totalBits fmt+DepotRAM.chartBits fmt)*(e).oldLanes))) :
    Covers R (joinFactor (fmt).degree) q.joinPrice := by
  let work:=32+40*P
  have stamps:=tableCost one (left 2 page)
  have clock:=add (constant one 4) (right rows (2*work+4))
  simpa only [joinFactor,joinPrice,Nat.mul_one,Nat.one_mul] using
    add (add stamps clock) (left 7 (constant one (11+4*work)))

theorem map_rows {R : ℕ} (one : 1≤R) (rows : Covers R 1 (e).nextRows)
    (page : Covers R 1 (2^(((e).fieldBits*(e).blocks+(e).fieldBits)*(e).lanes))) :
    Covers R (mapFactor (e).blocks (e).reach) q.mapPrice := by
  simpa only [MaterialExtent.nextRows,mapPrice,mapFactor,Nat.mul_one] using
    add (add (tableCost one (left ((2*(e).blocks)*2) page)) (tableCost one rows))
      (tableCost one (left ((e).reach+1) rows))

theorem sheets_rows (base w : ℕ) {R : ℕ} (one : 1≤R) (rows : Covers R 1 (e).sourceRows)
    (page : Covers R 1 (2^((DepotRAM.totalBits fmt+DepotRAM.chartBits fmt)*(e).oldLanes))) :
    Covers R (sheetFactor (DepotRAM.Material.Sheets.count fmt)) (phaseCost (q.materialSheets base w)) := by
  let n:=DepotRAM.Material.Sheets.count fmt
  have raw:=DepotRAM.Material.Sheets.priced fmt q.setup (e).oldHosts (e).oldGroups (e).oldLanes w
    ((e).observationsStart base) (q.joinBank base)
  unfold phaseCost materialSheets
  rw [raw]
  have table:=left n (add page (pad one rows))
  have scan:=add (constant one 4) (left n (add (constant one 4) (left 44 rows)))
  have code:=add (left 15 (add table (constant one 1))) (constant one (15+n*(11+4*20)))
  simpa only [n,RoleScans.pitch,DepotRAM.Material.Sheets.bits,MaterialExtent.sourceRows,DescentDyadicSpan.span,sheetFactor,Nat.mul_one] using add (add (add (constant one 4) (left 10 table)) scan) (left 7 code)

end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
