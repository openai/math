import OAI.ThreeFlat.RAM.HistoryRefreshElectedScale

namespace OAI
/-! # Elected refresh batch execution and tariffs -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

open private rateBuild from OAI.ThreeFlat.RAM.HistoryRefreshBatch
open private batch_units_le batch_charge from OAI.ThreeFlat.RAM.HistoryRefreshBatchRates
open private elected_scale from OAI.ThreeFlat.RAM.HistoryRefreshElectedScale

section Elected
open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open HistoryPartySpecialization HistoryPartyTapeRun
variable {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar : ℕ}
  (tile : Tile K H e d b) (good : (Fin (e*k)→Bool)→Prop) (letter : (Fin (e*k)→Bool)→Fin s)
  (tp : b+(e*d+e*d)≤ar) (sp : e*k+s≤ar)
  (A : HistoryPartyBatch.Layout) (input : Memory W) (t : Fin (B+1))

local notation "SC" => MotifNativeCompactors.partialInput K r t.val
local notation "PC" => MotifNativeCompactors.partialInput K (r*d) t.val
local notation "lib" => HistoryStaticArchive.all K ar

section Checks
local notation "X" => electedBatch tile good letter tp sp A input true
variable (read : Reads (electedBatch tile good letter tp sp A input true).regs
    (numeric (electedBatch tile good letter tp sp A input true).bootImage)
    (HistoryStaticArchive.all K ar) r t) (z : Histogram (Fin s) r)
local notation "dims[" hd "]" =>
  checks_fields tile good letter tp sp (X).regs (numeric (X).bootImage) t hd
local notation "comps[" histogram "]" => components good letter SC histogram
local notation "nets[" histogram "]" => fun i=>(comps[histogram] i).net
local notation "wires[" histogram "]" => fun i=>(comps[histogram] i).wire
local notation "ix[" hd "]" => Fin.cast (congrArg₂ Nat.add (dims[hd]).1 (dims[hd]).2.1)
local notation "ops[" hd "," histogram "]" =>
  HistoryPartyTapeRun.jobs (w:=W) (X).table (fun i=>(comps[histogram] (ix[hd] i)).net)
    (fun i=>(comps[histogram] (ix[hd] i)).wire) tag

include read in
/-- The elected checks branch reads the real LUT page, count page, and selected histogram
and emits the admission tree's rows and four-word root. -/
theorem checks_batch (small : r≤2^t.val) (lut : (X).regs.lutStride=HistoryStaticArchive.stride ar)
    (comp : (X).regs.compStride=StableCompactROMPool.page B 12)
    (quota : ∀ a : Fin s,numeric (X).bootImage (numeric (X).bootImage ((X).regs.incident+1)+a.val)=(z.val a).val)
    (room : BatchRoom X _ nets[z] wires[z] tag lib t (X).regs.lutBase (X).regs.compBase (dims[read]).1 (dims[read]).2.1) :
    let T := admission good letter SC z
    let base := dest A true (numeric input A.cursor-1) 0+4*T.rows
    (HistoryPartyBatch.procedure W A true).Exec input ((X).published ops[read,z]) ((X).cost ops[read,z]) ∧
      (∀ j : Fin 4,(X).published ops[read,z] ((X).target+j.val)=(Info.words ⟨base,r*(e*k),T.rows,T.bits⟩ j:Word W)) ∧
      HistoryCompiledRows.Records tag T.compile base ((X).published ops[read,z]) := by
  have sizes:=checks_dimensions tile good letter tp sp (X).regs (numeric (X).bootImage) t read z
  have model:=checks_models tile good letter tp sp (X).regs (numeric (X).bootImage) t read z small lut comp quota
  have infoEq:=batch_info X _ nets[z] wires[z] (dims[read]).1 (dims[read]).2.1 sizes (dims[read]).2.2.1 (dims[read]).2.2.2.1
  obtain ⟨exec,headers,records⟩:=batch_exec X _ nets[z] wires[z] tag lib _ t r (X).regs.lutBase (X).regs.compBase
    (dims[read]).1 (dims[read]).2.1 model sizes (dims[read]).2.2.1 (dims[read]).2.2.2.1 room
  rw [infoEq] at headers records
  exact ⟨exec,headers,records⟩

include read in
theorem checks_batch_tariff
    (room : BatchRoom X _ nets[z] wires[z] tag lib t (X).regs.lutBase (X).regs.compBase (dims[read]).1 (dims[read]).2.1) :
    (X).cost ops[read,z]+gatherRate*(r*(e*k)+4*(admission good letter SC z).rows) ≤
      (batchRate true+gatherRate)*batchUnits (e*k+s) s 1 d (e*k)*((W+1)^3*(1+r)) := by
  obtain ⟨dyadic,level,width⟩ := elected_scale tile good letter tp sp A input t true ops[read,z] read room.seed
  have sizes := checks_dimensions tile good letter tp sp (X).regs (numeric (X).bootImage) t read z
  have root := batch_info X _ nets[z] wires[z] (dims[read]).1 (dims[read]).2.1 sizes (dims[read]).2.2.1 (dims[read]).2.2.2.1
  have row : (admission good letter SC z).rows=(X).table.r*(X).table.left.rows+(X).table.s*(X).table.right.rows :=
    (congrArg Info.factors root).symm
  have sc : (X).staticCost=batchRate true := (X).staticCost_eq (rateBuild true) rfl
  have cost := (X).typed_cost_le (fun i=>(comps[z] (ix[read] i)).net)
    (fun i=>(comps[z] (ix[read] i)).wire) tag room.count
  rw [sc] at cost
  apply batch_charge cost
  have clock : Nat.clog 2 (HistoryPartyBootExec.extent (X).layout (numeric (X).input))=t.val := dyadic
  have copies : (X).table.r=r := (dims[read]).1
  have groups : (X).table.s=s := (dims[read]).2.1
  have lutShape : (X).table.left=BatchRows.lutSize (e*k+s) := (dims[read]).2.2.2.2.1
  have compShape : (X).table.right=BatchRows.compSize SC := (dims[read]).2.2.2.2.2
  rw [row,clock,←room.count,copies,groups,lutShape,compShape]
  have cap := batch_units_le r d W t.val (e*k+s) s 1 (e*k) (SC).cells level width
    (MotifNativeCompactors.partialInput_rows (F:=K) r t.val)
  simpa only [BatchRows.lutSize,BatchRows.compSize,Nat.mul_one,
    show r+(r+r)=3*r by omega] using cap

end Checks

section Payload
local notation "X" => electedBatch tile good letter tp sp A input false
variable (read : Reads (electedBatch tile good letter tp sp A input false).regs
  (numeric (electedBatch tile good letter tp sp A input false).bootImage) (HistoryStaticArchive.all K ar) r t)
include read
local notation "dims" => (fun evidence => payload_fields (r:=r) tile good letter tp sp
  (X).regs (numeric (X).bootImage) t evidence)
local notation "comps" => pieces (checkedTile tile.rule tile.table) PC
local notation "nets" => fun i=>(comps i).N
local notation "wires" => fun i=>(comps i).wire
local notation "ix" => (fun evidence => Fin.cast (congrArg₂ Nat.add (dims evidence).1 (dims evidence).2.1))
local notation "ops" => (fun evidence => HistoryPartyTapeRun.jobs (w:=W) (X).table
  (fun i=>(comps (ix evidence i)).N) (fun i=>(comps (ix evidence i)).wire) tag)

/-- The elected payload branch emits the real tile and shortened stream compactor. -/
theorem payload_batch (small : r*d≤2^t.val) (lut : (X).regs.lutStride=HistoryStaticArchive.stride ar)
    (comp : (X).regs.compStride=StableCompactROMPool.page B 12)
    (room : BatchRoom X _ nets wires tag lib t (X).regs.lutBase (X).regs.compBase (dims read).1 (dims read).2.1) :
    let T:=tiled tile PC
    let base:=dest A false (numeric input A.cursor-1) 0+4*T.rows
    (HistoryPartyBatch.procedure W A false).Exec input ((X).published (ops read)) ((X).cost (ops read)) ∧
      (∀ j : Fin 4,(X).published (ops read) ((X).target+j.val)=(Info.words ⟨base,r*b+e*(r*d),T.rows,T.bits⟩ j:Word W)) ∧
      HistoryCompiledRows.Records tag T.compile base ((X).published (ops read)) := by
  have sizes:=payload_dimensions tile good letter tp sp (X).regs (numeric (X).bootImage) t read
  have model:=payload_models tile good letter tp sp (X).regs (numeric (X).bootImage) t read small lut comp
  have shared : (X).table.shared=e*(r*d)+e*(r*d) := (dims read).2.2.2.1.trans (two_mul _)
  have infoEq:=batch_info X _ nets wires (dims read).1 (dims read).2.1 sizes (dims read).2.2.1 shared
  obtain ⟨exec,headers,records⟩:=batch_exec X _ nets wires tag lib _ t (r*d) (X).regs.lutBase (X).regs.compBase
    (dims read).1 (dims read).2.1 model sizes (dims read).2.2.1 shared room
  rw [infoEq] at headers records
  exact ⟨exec,headers,records⟩

theorem payload_batch_tariff
    (room : BatchRoom X _ nets wires tag lib t (X).regs.lutBase (X).regs.compBase (dims read).1 (dims read).2.1) :
    (X).cost (ops read)+gatherRate*(r*b+e*(r*d)+4*(tiled tile PC).rows) ≤
      (batchRate false+gatherRate)*batchUnits (b+(e*d+e*d)) e d d (b+e*d)*((W+1)^3*(1+r)) := by
  obtain ⟨dyadic,level,width⟩ := elected_scale tile good letter tp sp A input t false (ops read) read room.seed
  have sizes := payload_dimensions tile good letter tp sp (X).regs (numeric (X).bootImage) t read
  have shared : (X).table.shared=e*(r*d)+e*(r*d) := (dims read).2.2.2.1.trans (two_mul _)
  have root := batch_info X _ nets wires (dims read).1 (dims read).2.1 sizes (dims read).2.2.1 shared
  have row : (tiled tile PC).rows=(X).table.r*(X).table.left.rows+(X).table.s*(X).table.right.rows :=
    (congrArg Info.factors root).symm
  have sc : (X).staticCost=batchRate false := (X).staticCost_eq (rateBuild false) rfl
  rw [←sc]
  apply batch_charge ((X).typed_cost_le (fun i=>(comps (ix read i)).N) (fun i=>(comps (ix read i)).wire) tag room.count)
  have clock : Nat.clog 2 (HistoryPartyBootExec.extent (X).layout (numeric (X).input))=t.val := dyadic
  have copies : (X).table.r=r := (dims read).1
  have groups : (X).table.s=e := (dims read).2.1
  have lutShape : (X).table.left=BatchRows.lutSize (b+(e*d+e*d)) := (dims read).2.2.2.2.1
  have compShape : (X).table.right=BatchRows.compSize PC := (dims read).2.2.2.2.2
  rw [row,clock,←room.count,copies,groups,lutShape,compShape]
  have cap := batch_units_le r d W t.val (b+(e*d+e*d)) e d (b+e*d) (PC).cells level width
    (MotifNativeCompactors.partialInput_rows (F:=K) (r*d) t.val)
  dsimp only [BatchRows.lutSize,BatchRows.compSize] at cap ⊢
  convert cap using 1; ring

end Payload
end Elected


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
