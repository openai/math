import OAI.ThreeFlat.RAM.HistoryRefreshElectedScale

namespace OAI
/-! # Native jobs of the elected refresh batches -/
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

section LiveArm
open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open HistoryPartySpecialization
private def reindexedJobs {K : Type} {n hidden pins : ℕ} (Q : HistoryPartyBatchExec.Build W)
    (count : Q.table.r + Q.table.s = n) (width : Fin n → ℕ)
    (nets : ∀ i : Fin n, BitNetwork K (width i))
    (wires : ∀ i : Fin n, Fin (width i) → BitSource hidden pins)
    (code : ((Fin 3 → Bool) → K) → ℕ) : List (HistoryReadyTape.Job W) :=
  HistoryPartyTapeRun.jobs (w := W) Q.table (arity := fun i => width (Fin.cast count i))
    (fun i => nets (Fin.cast count i)) (fun i => wires (Fin.cast count i)) code

private def liveCheckJobs {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar : ℕ}
    (tile : Tile K H e d b) (good : (Fin (e*k) → Bool) → Prop) (letter : (Fin (e*k) → Bool) → Fin s)
    (tp : b+(e*d+e*d) ≤ ar) (sp : e*k+s ≤ ar) (A : HistoryPartyBatch.Layout)
    (mem : Memory W) (t : Fin (B+1)) (z : Histogram (Fin s) r)
    (read : Reads (electedBatch tile good letter tp sp A mem true).regs
      (numeric (electedBatch tile good letter tp sp A mem true).bootImage) (HistoryStaticArchive.all K ar) r t) :
    List (HistoryReadyTape.Job W) :=
  let Q := electedBatch tile good letter tp sp A mem true
  let dims := checks_fields tile good letter tp sp Q.regs (numeric Q.bootImage) t read
  let parts := components good letter (MotifNativeCompactors.partialInput K r t.val) z
  reindexedJobs Q (congrArg₂ Nat.add dims.1 dims.2.1) (fun i => (parts i).width)
    (fun i => (parts i).net) (fun i => (parts i).wire) (tag (K := K))

private def livePayloadJobs {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar : ℕ}
    (tile : Tile K H e d b) (good : (Fin (e*k) → Bool) → Prop) (letter : (Fin (e*k) → Bool) → Fin s)
    (tp : b+(e*d+e*d) ≤ ar) (sp : e*k+s ≤ ar) (A : HistoryPartyBatch.Layout)
    (mem : Memory W) (t : Fin (B+1))
    (read : Reads (electedBatch tile good letter tp sp A mem false).regs
      (numeric (electedBatch tile good letter tp sp A mem false).bootImage) (HistoryStaticArchive.all K ar) r t) :
    List (HistoryReadyTape.Job W) :=
  let Q := electedBatch tile good letter tp sp A mem false
  let dims := payload_fields tile good letter tp sp Q.regs (numeric Q.bootImage) t read
  let parts := pieces (r := r) (checkedTile tile.rule tile.table) (MotifNativeCompactors.partialInput K (r*d) t.val)
  reindexedJobs Q (congrArg₂ Nat.add dims.1 dims.2.1) (fun i => (parts i).width)
    (fun i => (parts i).N) (fun i => (parts i).wire) (tag (K := K))

end LiveArm

end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
