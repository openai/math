import OAI.ThreeFlat.RAM.TickAuxRequestGen
import OAI.ThreeFlat.RAM.TickCheckedBank

namespace OAI
/-! # Running the assembled auxiliary guard in its actual continuation ROM -/

namespace ThreeFlat.RAM.TickAuxRequestGen

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan ChunkRequests TickBitRelation
open Diagonal.TickChronology Diagonal.TickAuxiliary
open scoped Classical

open scoped Fin.CommRing

variable {F : Type*} [Semiring F] {w k pc r a : ℕ}

theorem mass_bank (field : FieldCode F w) (M : Machine w pc r k) (A : Layout a) (ph : Phase)
    (addr : Fin 4 → Word w) (start : ℕ) (old new : Word w) (x y : Fin a → Bool)
    (P : Fin (TickCheckedBank.count (TickRequestStream.program start (row (k:=k) addr))) ↪ Fin pc)
    (G : Fin (4+(TickRequestStream.program start (row (k:=k) addr)).binds) ↪ Fin r)
    (R : Fin 37 ↪ Fin r) (exit : Fin pc)
    (rom : TickCheckedBank.Installed M (TickRequestStream.program start (row addr))
      (start : Word w) (start+8*a : ℕ) old new P G R exit)
    (c : Config w pc r) (m : Memory w)
    (entry : c.pc = TickGenerateTable.driver _ (TickCheckedBank.generatePC _ P) 0)
    (wide : 64 ≤ 2^w) (fit : start+8*a < 2^w)
    (headerSafe : ∀ j, (addr j).val < start)
    (hdr : ∀ j, m (addr j).val = header A ph true j)
    (oldSafe : ∀ i : Fin a, (old+(i.val : Word w)).val < start)
    (newSafe : ∀ i : Fin a, (new+(i.val : Word w)).val < start)
    (readOld : ∀ i : Fin a, bitAt m old (i.val : Word w) = bitWord w (x i))
    (readNew : ∀ i : Fin a, bitAt m new (i.val : Word w) = bitWord w (y i)) :
    let filled := fillSegment start (8*a) (TickRequestStream.dataWord start (A.rule ph true)) m
    ∃ t ≤ 14+a*5082, ∃ out : Config w pc r, out.pc = exit ∧
      ∀ fuel, mass field M.program (fuel+t) c m =
        if A.accepts ph true x y then mass field M.program fuel out filled else 0 :=
  mass_aux field M A ph true addr start old new x y c m wide fit
    (TickCheckedBank.generatePC _ P) G (TickCheckedBank.setupPC _ P)
    (linkedRegisters w k R) (linkedLabels w k (TickCheckedBank.scanPC _ P)) (R 36)
    (linkedControl (TickCheckedBank.scanPC _ P) 3) (linkedControl (TickCheckedBank.scanPC _ P) 4) exit
    rom.gen rom.setup rom.check entry headerSafe hdr oldSafe newSafe readOld readNew


end ThreeFlat.RAM.TickAuxRequestGen

end OAI
