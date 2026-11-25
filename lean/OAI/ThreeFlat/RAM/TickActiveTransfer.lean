import OAI.ThreeFlat.RAM.TickActiveROM
import OAI.ThreeFlat.RAM.TickHistoryRun
import OAI.ThreeFlat.RAM.TickGroupScanBank
import OAI.ThreeFlat.RAM.TickEvaluationRun

namespace OAI
/-! # Exact transfer weight of every active physical branch after admission -/

noncomputable section
namespace ThreeFlat.RAM.TickActiveROM
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink DescriptorScan TickFuel Diagonal.TickChronology
open Contraction BitLayout HistoryFactors
open Diagonal.TickGroupIntervals (Interval)
open TickChunkCheck (chunkSize)
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] [Fintype F] {p H J w k n m nr mr r pc : ℕ}

/-- A bit vector viewed through the size equality for the actual rotated
interval lookup. -/
def chunkView (B : Layout) (lo g : ℕ) (x : Fin B.bits → Bool) :
    Fin (chunkSize (TickGroupScanBank.layout B.scan lo g)) → Bool :=
  fun i => x (Fin.cast (TickGroupScanBank.size B.scan lo g) i)

theorem active_transfer (B : Layout) (clock : Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)
    (M : Machine w pc r k) (nav : Block w n nr k) (prep : Block w m mr k)
    (P : Labels (n:=n) (m:=m) (k:=k) B clock fit ↪ Fin pc)
    (R : Registers B clock fit nr mr r k) (K : Fin 7 → Fin k)
    (rom : ∀ i, M.code (P i) = emit B clock fit nav prep P R K i)
    (ph : Phase) (L : Diagonal.TickAuxiliary.Layout B.bits)
    (d : Config w pc r) (mem : Memory w) (oa na oc nc : Fin B.bits → Bool)
    (entry : d.pc = TickHistoryCore.resumeAux (B.aux w k)
      (inside P .control (fun _ _ h => by cases h; rfl)))
    (width : 64 ≤ 2^w) (auxFit : B.auxRequest+8*B.bits < 2^w)
    (headSafe : ∀ j, (B.header w j).val < B.auxRequest)
    (header : ∀ j, mem (B.header w j).val = TickAuxRequestGen.header L ph true j)
    (oldSafe : ∀ i : Fin B.bits, ((B.oldAux : Word w)+(i.val : Word w)).val < B.auxRequest)
    (newSafe : ∀ i : Fin B.bits, ((B.newAux : Word w)+(i.val : Word w)).val < B.auxRequest)
    (oldAux : ∀ i : Fin B.bits, ChunkRequests.bitAt mem B.oldAux (i.val : Word w) = TickBitRelation.bitWord w (oa i))
    (newAux : ∀ i : Fin B.bits, ChunkRequests.bitAt mem B.newAux (i.val : Word w) = TickBitRelation.bitWord w (na i))
    (oldSpace : B.oldChunk+B.bits ≤ B.auxRequest) (newSpace : B.newChunk+B.bits ≤ B.auxRequest)
    (oldChunk : ∀ i : Fin B.bits, mem (B.oldChunk+i.val) = TickBitRelation.bitWord w (oc i))
    (newChunk : ∀ i : Fin B.bits, mem (B.newChunk+i.val) = TickBitRelation.bitWord w (nc i))
    (es : List Interval) (lo g : ℕ) (op np : ℕ → Bool)
    (onScan : ph=.scan → TickGroupScanBank.ScanInputs w B.scan es lo g
      (fillSegment B.auxRequest (8*B.bits) (TickRequestStream.dataWord B.auxRequest (L.rule ph true)) mem)
      op np (chunkView B lo g oc) (chunkView B lo g nc))
    (N : BitNetwork F p) (lib : Library N) (pin : Fin p → Bool)
    (hn : N.internal=H) (hc : N.cells=J)
    (hm : footprint (TickWeightedBank.shape F p H J) ≤ B.metadata)
    (hl : footprint (TickWeightedBank.shape F p H J) ≤ B.lut)
    (bm : B.metadata+4*J ≤ 2^w) (bl : B.lut+8*lib.count ≤ 2^w)
    (space : footprint (TickWeightedBank.shape F p H J) < 2^w)
    (par : ∀ i, M.publicData (K i) = (interpreter p H J B.metadata B.lut (F:=F) fit).publicData i)
    (invariant : Memory w → Prop) (budget : ℕ)
    (prepared : TickStageSpec.Prepare prep M.publicData invariant
      (fun _ m => TickWeightedBank.Ready fit N lib pin B.metadata B.lut m) budget)
    (onEval : ph=.evaluate → invariant (fillSegment B.auxRequest (8*B.bits)
      (TickRequestStream.dataWord B.auxRequest (L.rule ph true)) mem)) :
    let field := codec (TickWeightedBank.shape F p H J) fit
    let q := Fintype.card F
    Returns field M.program ((14+B.bits*5082)+(17+6*B.bits+max (30+20*es.length+4319*B.bits)
      (budget+(53+(q*q)*(6*(q*q)+10)+5*H+550*J)))) d mem
      (if L.accepts ph true oa na then
        if ph=.scan then (if TickChunkCheck.valid true (TickGroupScanBank.layout B.scan lo g) es op np
          (chunkView B lo g oc) (chunkView B lo g nc) then 1 else 0)
        else if oc=nc then (if ph=.evaluate then N.eval pin else 1) else 0
       else 0) := by
  let core := inside P Label.control (fun _ _ h => by cases h; rfl)
  let scan := inside P Label.readChunk (fun _ _ h => by cases h; rfl)
  let ev := inside P Label.prepare (fun _ _ h => by cases h; rfl)
  let terminal := inside P Label.run (fun _ _ h => by cases h; rfl)
  let clk := inside P Label.writeClock (fun _ _ h => by cases h; rfl)
  let field := codec (TickWeightedBank.shape F p H J) fit
  let aux := B.aux w k
  apply TickHistoryCore.after_navigation field M L ph B.auxRequest B.regions (range w B.control)
    (B.header w) core R.control R.generator R.compare R.test R.chunks (TickGenerateTable.driver _ clk 0)
    (TickGroupScanBank.boot B.scan scan 0) (ev prep.first) (fun i => rom (.control i)) d mem oa na oc nc
    entry width auxFit headSafe header oldSafe newSafe oldAux newAux oldSpace newSpace oldChunk newChunk
  · intro hp b here
    exact TickGroupScanBank.returns field M B.scan scan R.scan R.scanGen R.compare
      (TickHistoryCore.returned aux core) (fun i => rom (.readChunk i))
      (rom (.control (.inr (.inr (.inr (.inr 0)))))) es lo g b _ op np _ _ here (onScan hp)
  · intro hp b here
    exact TickWeightedBank.after_prepare M fit B.metadata B.lut hm hl N lib hn hc bm bl space pin
      terminal R.field R.eval K (fun i => rom (.run i)) par prep ev R.slot
      (fun i => rom (.prepare i)) invariant budget prepared b _ here (onEval hp)


end ThreeFlat.RAM.TickActiveROM

end
end OAI
