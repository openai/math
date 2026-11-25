import OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs
import OAI.ThreeFlat.RAM.HistoryRefreshPairRoom

namespace OAI
/-! # Published memory, cost and address bounds of an elected refresh party -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000
set_option Elab.async false

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

open private liveCheckJobs livePayloadJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs

section LiveArm
open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open HistoryPartySpecialization
variable {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar : ℕ}
  (tile : Tile K H e d b) (good : (Fin (e*k)→Bool)→Prop) (letter : (Fin (e*k)→Bool)→Fin s)
  (tp : b+(e*d+e*d)≤ar) (sp : e*k+s≤ar) (A : HistoryPartyBatch.Layout) (node : ℕ)
  (input : Memory W) (t : Fin (B+1)) (z : Histogram (Fin s) r)
local notation "lib" => HistoryStaticArchive.all K ar
local notation "X" => electedBatch tile good letter tp sp A input true
variable (readC : Reads (electedBatch tile good letter tp sp A input true).regs
  (numeric (electedBatch tile good letter tp sp A input true).bootImage) (HistoryStaticArchive.all K ar) r t)
local notation "SC" => MotifNativeCompactors.partialInput K r t.val
local notation "PC" => MotifNativeCompactors.partialInput K (r*d) t.val
local notation "L" => admission good letter SC z
local notation "R" => tiled tile PC
local notation "a₀" => r*(e*k)
local notation "b₀" => r*b+e*(r*d)
local notation "dimsC" => checks_fields tile good letter tp sp (X).regs (numeric (X).bootImage) t readC
local notation "compsC" => components good letter SC z
local notation "jobsC" => liveCheckJobs tile good letter tp sp A input t z readC
local notation "postC" => (X).published jobsC
local notation "Y" => electedBatch tile good letter tp sp A postC false
variable (readP : Reads (electedBatch tile good letter tp sp A ((electedBatch tile good letter tp sp A input true).published (liveCheckJobs tile good letter tp sp A input t z readC)) false).regs
  (numeric (electedBatch tile good letter tp sp A ((electedBatch tile good letter tp sp A input true).published (liveCheckJobs tile good letter tp sp A input t z readC)) false).bootImage) (HistoryStaticArchive.all K ar) r t)
local notation "dimsP" => payload_fields tile good letter tp sp (Y).regs (numeric (Y).bootImage) t readP
local notation "compsP" => pieces (checkedTile tile.rule tile.table) PC
local notation "jobsP" => livePayloadJobs tile good letter tp sp A postC t readP
local notation "postP" => (Y).published jobsP
local notation "builder" => HistoryPartyPairExec.build A node a₀ b₀ postP
local notation "pairJobs" => HistoryPartyPairExec.steps (w:=W) A node L R tag

def electedOutput : Memory W :=
  let check := electedBatch tile good letter tp sp A input true
  let middle := check.published (liveCheckJobs tile good letter tp sp A input t z readC)
  let payload := electedBatch tile good letter tp sp A middle false
  let final := payload.published (livePayloadJobs tile good letter tp sp A middle t readP)
  (HistoryPartyPairExec.build A node a₀ b₀ final).output pairJobs

def electedCost : ℕ :=
  let check := electedBatch tile good letter tp sp A input true
  let checks := liveCheckJobs tile good letter tp sp A input t z readC
  let middle := check.published checks
  let payload := electedBatch tile good letter tp sp A middle false
  let payloads := livePayloadJobs tile good letter tp sp A middle t readP
  check.cost checks + payload.cost payloads +
    HistoryPartyPairExec.overhead A W * (1+a₀+b₀+4*((L).rows+(R).rows))

/-- Complete resident-data chart of the live checks and payload. It names the actual
header page, lookup and compactor, and protects the earlier checks output through the payload. -/
structure ElectedRoom : Prop where
  copy : r≤2^t.val
  digit : r*d≤2^t.val
  lutC : (X).regs.lutStride=HistoryStaticArchive.stride ar
  lutP : (Y).regs.lutStride=HistoryStaticArchive.stride ar
  strideC : (X).regs.compStride=StableCompactROMPool.page B 12
  strideP : (Y).regs.compStride=StableCompactROMPool.page B 12
  quota : ∀ a : Fin s,numeric (X).bootImage (numeric (X).bootImage ((X).regs.incident+1)+a.val)=(z.val a).val
  before : numeric input A.cursor-1=node
  middle : numeric postC A.cursor-1=node
  checks : BatchRoom X (fun i : Fin (r+s) => (compsC i).width) (fun i => (compsC i).net)
    (fun i => (compsC i).wire) tag lib t (X).regs.lutBase (X).regs.compBase
    (checks_fields tile good letter tp sp (X).regs (numeric (X).bootImage) t readC).1
    (checks_fields tile good letter tp sp (X).regs (numeric (X).bootImage) t readC).2.1
  payload : BatchRoom Y (fun i : Fin (r+e) => (compsP i).width) (fun i => (compsP i).N)
    (fun i => (compsP i).wire) tag lib t (Y).regs.lutBase (Y).regs.compBase
    (payload_fields tile good letter tp sp (Y).regs (numeric (Y).bootImage) t readP).1
    (payload_fields tile good letter tp sp (Y).regs (numeric (Y).bootImage) t readP).2.1
  checksInfo : ∀ j : Fin 4,BatchAway Y jobsP (dest A true node 1+j.val)
  checksRows : ∀ i : Fin (L).compile.cells,∀ j : Fin 4,BatchAway Y jobsP (dest A true node 0+4*(L).rows+(4*i.val+j.val))
  pair : PairRoom A node L R tag postP

end LiveArm

end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
