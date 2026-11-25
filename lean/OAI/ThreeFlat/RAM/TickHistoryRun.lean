import OAI.ThreeFlat.RAM.TickAfterAux
import OAI.ThreeFlat.RAM.TickAuxBankRun

namespace OAI
/-! # Shared guard, pair scan and terminal evaluation in the same emitted text -/

namespace ThreeFlat.RAM.TickHistoryCore

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan Diagonal.TickChronology Diagonal.TickAuxiliary
open ChunkRequests TickBitRelation TickFuel
open scoped Classical Fin.CommRing

variable {F : Type*} [Semiring F] {w k r pc a : ℕ}

theorem after_navigation (field : FieldCode F w) (M : Machine w pc r k) (A : Layout a) (ph : Phase)
    (start : ℕ) (regions : TickIdentity.Regions) (dest header : Fin 4 → Word w)
    (P : Labels (TickRequestStream.program start (TickAuxRequestGen.row (k:=k) header)) ↪ Fin pc)
    (hReg : Fin 5 ↪ Fin r) (gen : Fin (4+(TickRequestStream.program start
      (TickAuxRequestGen.row (k:=k) header)).binds) ↪ Fin r) (ck : Fin 37 ↪ Fin r)
    (testReg : Fin 2 ↪ Fin r) (cmp : Fin 7 ↪ Fin r) (nav scan ev : Fin pc)
    (rom : ∀ i, M.code (P i) = emit a start regions dest header P hReg gen ck testReg cmp nav scan ev i)
    (cfg : Config w pc r) (mem : Memory w) (oa na oc nc : Fin a → Bool)
    (entry : cfg.pc = resumeAux _ P)
    (wide : 64 ≤ 2^w) (fit : start+8*a < 2^w)
    (safeHeader : ∀ j, (header j).val < start)
    (hdr : ∀ j, mem (header j).val = TickAuxRequestGen.header A ph true j)
    (safeOld : ∀ i : Fin a, ((regions.oldAux : Word w)+(i.val : Word w)).val < start)
    (safeNew : ∀ i : Fin a, ((regions.newAux : Word w)+(i.val : Word w)).val < start)
    (readOld : ∀ i : Fin a, bitAt mem regions.oldAux (i.val : Word w) = bitWord w (oa i))
    (readNew : ∀ i : Fin a, bitAt mem regions.newAux (i.val : Word w) = bitWord w (na i))
    (safeOC : regions.oldChunk+a ≤ start) (safeNC : regions.newChunk+a ≤ start)
    (readOC : ∀ i : Fin a, mem (regions.oldChunk+i.val) = bitWord w (oc i))
    (readNC : ∀ i : Fin a, mem (regions.newChunk+i.val) = bitWord w (nc i))
    (timeScan timeEval : ℕ) (vScan vEval : F)
    (passScan : ph=.scan → ∀ d : Config w pc r, d.pc=scan → Returns field M.program timeScan d
      (fillSegment start (8*a) (TickRequestStream.dataWord start (A.rule ph true)) mem) vScan)
    (passEval : ph=.evaluate → ∀ d : Config w pc r, d.pc=ev → Returns field M.program timeEval d
      (fillSegment start (8*a) (TickRequestStream.dataWord start (A.rule ph true)) mem) vEval) :
    Returns field M.program ((14+a*5082)+(17+6*a+max timeScan timeEval)) cfg mem
      (if A.accepts ph true oa na then
        if ph=.scan then vScan else if oc=nc then (if ph=.evaluate then vEval else 1) else 0
       else 0) := by
  let e := TickRequestStream.program start (TickAuxRequestGen.row (k:=k) header)
  let filled := fillSegment start (8*a) (TickRequestStream.dataWord start (A.rule ph true)) mem
  have bank : TickCheckedBank.Installed M e (start : Word w) (start+8*a : ℕ) regions.oldAux regions.newAux
      (checked e P) gen ck (test e P false 0) := ⟨fun i => rom (.inr (.inl i))⟩
  obtain ⟨steps,limit,out,outPC,guard⟩ := TickAuxRequestGen.mass_bank field M A ph header start
    regions.oldAux regions.newAux oa na (checked e P) gen ck _ bank cfg mem entry wide fit
    safeHeader hdr safeOld safeNew readOld readNew
  have low (j : ℕ) (hj : j<start) : filled j = mem j := by
    simp [filled,fillSegment,show ¬start ≤ j by omega]
  have tag : filled (header 0).val = (ph.tag : Word w) :=
    (low _ (safeHeader 0)).trans (hdr 0)
  have rest := after_aux field M ph (header 0) (test e P false) (test e P true) testReg
    (chunk e P) cmp regions.oldChunk regions.newChunk scan ev (returned e P) timeScan timeEval vScan vEval
    (fun i => rom (.inr (.inr (.inl (false,i)))))
    (fun i => rom (.inr (.inr (.inl (true,i)))))
    (fun i => rom (.inr (.inr (.inr (.inl i))))) (rom (.inr (.inr (.inr (.inr 0)))))
    out filled oc nc outPC tag (by omega) (by omega) (by omega)
    (fun i => (low _ (by have := i.isLt; omega)).trans (readOC i))
    (fun i => (low _ (by have := i.isLt; omega)).trans (readNC i)) passScan passEval
  exact (Returns.guard _ guard rest).later (by omega)


end ThreeFlat.RAM.TickHistoryCore

end OAI
