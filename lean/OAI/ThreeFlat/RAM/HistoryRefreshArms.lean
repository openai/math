import OAI.ThreeFlat.RAM.HistoryRefreshElectedRoom
import OAI.ThreeFlat.RAM.HistoryRefreshElectedBatch

namespace OAI
/-! # Execution of an elected refresh party -/
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

open private tariffLayout from OAI.ThreeFlat.RAM.HistoryRefreshBatch

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

private abbrev batchAt {K : Type*} [CommRing K] {width W : ℕ} (A : HistoryPartyBatch.Layout)
    (side : Bool) (T : Tree K width) (code : ((Fin 3 → Bool) → K) → ℕ)
    (n : ℕ) (input output : Memory W) (ticks : ℕ) : Prop :=
  let base := dest A side n 0 + 4 * T.rows
  (HistoryPartyBatch.procedure W A side).Exec input output ticks ∧
    (∀ j : Fin 4, output (dest A side n 1 + j.val) =
      (Info.words ⟨base, width, T.rows, T.bits⟩ j : Word W)) ∧
    HistoryCompiledRows.Records code T.compile base output

private theorem batchAt_cursor {K : Type*} [CommRing K] {width W : ℕ} (A : HistoryPartyBatch.Layout)
    (side : Bool) (T : Tree K width) (code : ((Fin 3 → Bool) → K) → ℕ)
    (old node : ℕ) (input output : Memory W) (ticks : ℕ) (position : old = node)
    (issued : batchAt A side T code old input output ticks) :
    batchAt A side T code node input output ticks := by
  cases position
  exact issued

section Assembly

attribute [local irreducible] HistoryPartyBatchExec.Build.published HistoryPartyBatchExec.Build.cost
  HistoryPartyTapeRun.jobs HistoryBoundedBody.Build.output HistoryPartyPairExec.build HistoryPartyPairExec.steps
  HistoryPartyBatch.procedure HistoryPartyPair.procedure

/-- The live root and row stream are produced by the actual sequence of two selected
batches and a pair; each batch's leaf staging precedes its translated stream. -/
theorem elected_arm (room : ElectedRoom tile good letter tp sp A node input t z readC readP) :
    (HistoryPartyPair.procedure W A).Exec input (electedOutput tile good letter tp sp A node input t z readC readP)
      (electedCost tile good letter tp sp A input t z readC readP) ∧
    (∀ j : Fin 4,(builder).output pairJobs (HistoryPartyPair.atPair A node 1+j.val)=
      (Info.words ⟨HistoryPartyPair.atPair A node 0,a₀+b₀,(L).rows+(R).rows,(L).bits+(R).bits⟩ j:Word W)) ∧
    HistoryCompiledRows.Records tag (pair L R).compile (HistoryPartyPair.atPair A node 0) ((builder).output pairJobs) := by
  have checked : batchAt A true L tag node input postC ((X).cost jobsC) :=
    batchAt_cursor A true L tag (numeric input A.cursor-1) node input postC ((X).cost jobsC) room.before
      (checks_batch tile good letter tp sp A input t readC z room.copy room.lutC room.strideC room.quota room.checks)
  have paid : batchAt A false R tag node postC postP ((Y).cost jobsP) :=
    batchAt_cursor A false R tag (numeric postC A.cursor-1) node postC postP ((Y).cost jobsP) room.middle
      (payload_batch tile good letter tp sp A postC t readP room.digit room.lutP room.strideP room.payload)
  exact elected_pair A node L R tag postP input postC ((X).cost jobsC) ((Y).cost jobsP)
    checked.1 paid.1
    (fun j => ((room.checksInfo j).keeps room.payload.seed.seedRoom).trans (checked.2.1 j))
    paid.2.1
    (fun i j => ((room.checksRows i j).keeps room.payload.seed.seedRoom).trans (checked.2.2 i j))
    paid.2.2 room.pair

end Assembly

private theorem elected_tariff_bound
    (checks payload checksPins payloadPins checksRows payloadRows overhead gather
      checksRate payloadRate widthFactor population : ℕ)
    (same : overhead = gather)
    (left : checks + gather*(checksPins+4*checksRows) ≤ checksRate*(widthFactor*population))
    (right : payload + gather*(payloadPins+4*payloadRows) ≤ payloadRate*(widthFactor*population))
    (positive : 0 < widthFactor*population) :
    checks+payload+overhead*(1+checksPins+payloadPins+4*(checksRows+payloadRows)) ≤
      (checksRate+payloadRate+gather)*widthFactor*population := by
  subst overhead
  calc
    _ = (checks+gather*(checksPins+4*checksRows))+
        (payload+gather*(payloadPins+4*payloadRows))+gather := by ring
    _ ≤ checksRate*(widthFactor*population)+payloadRate*(widthFactor*population)+
        gather*(widthFactor*population) :=
      Nat.add_le_add (Nat.add_le_add left right) (Nat.le_mul_of_pos_right gather positive)
    _ = _ := by ring

open private pair_overhead_rate from OAI.ThreeFlat.RAM.HistoryRefreshBatch

section ElectedTariff
attribute [local irreducible] HistoryPartyBatchExec.Build.cost HistoryPartyBatchExec.Build.published
  HistoryPartyPairExec.overhead batchRate batchUnits gatherRate

/-- Total native fee of the two elected batches in chronological memory and their final pair gather. -/
theorem elected_pair_tariff (room : ElectedRoom tile good letter tp sp A node input t z readC readP) :
    electedCost tile good letter tp sp A input t z readC readP ≤
      partyTariff s e k b d*(W+1)^3*(1+r) := by
  exact elected_tariff_bound ((X).cost jobsC) ((Y).cost jobsP) a₀ b₀ (L).rows (R).rows
    (HistoryPartyPairExec.overhead A W) gatherRate
    ((batchRate true+gatherRate)*batchUnits (e*k+s) s 1 d (e*k))
    ((batchRate false+gatherRate)*batchUnits (b+(e*d+e*d)) e d d (b+e*d))
    ((W+1)^3) (1+r) (pair_overhead_rate A W)
    (checks_batch_tariff tile good letter tp sp A input t readC z room.checks)
    (payload_batch_tariff tile good letter tp sp A postC t readP room.payload)
    (by positivity)

end ElectedTariff


end LiveArm

end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
