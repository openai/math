import OAI.ThreeFlat.RAM.TickHistoryCore
import OAI.ThreeFlat.RAM.TickChunkPreserve
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # Weighted semantics after the common physical auxiliary guard -/

namespace ThreeFlat.RAM.TickHistoryCore

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickChronology TickFuel
open scoped Classical Fin.CommRing

variable {F : Type*} [Semiring F] {w k r pc a : ℕ}

private theorem tag_eq (ph q : Phase) (wide : 7 ≤ 2^w) :
    ((ph.tag : Word w) = (q.tag : Word w)) ↔ ph=q := by
  have small (s : Phase) : s.tag < 2^w := by
    have hs : s.tag < 7 := by cases s <;> decide
    omega
  rw [Fin.ext_iff,Fin.val_cast_of_lt (small ph),Fin.val_cast_of_lt (small q)]
  cases ph <;> cases q <;> decide

/-- The actual two tag-read blocks and the seven-register chunk comparator
handle every phase. The scan and weighted computations use their supplied
native terminal semantics. -/
theorem after_aux (field : FieldCode F w) (M : Machine w pc r k) (ph : Phase)
    (phaseAddr : Word w) (T U : Fin 4 → Fin pc) (R : Fin 2 ↪ Fin r)
    (G : Fin 14 ↪ Fin pc) (cmp : Fin 7 ↪ Fin r) (left right : ℕ)
    (scan evaluation done : Fin pc) (timeScan timeEval : ℕ) (vScan vEval : F)
    (testRows : ∀ i, M.code (T i) = TickMarkerSwitch.emitOn T R phaseAddr
      (Phase.scan.tag : Word w) scan (G (TickIdentity.compare w left right a).first) i)
    (lastRows : ∀ i, M.code (U i) = TickMarkerSwitch.emitOn U R phaseAddr
      (Phase.evaluate.tag : Word w) evaluation done i)
    (chunkRows : (TickIdentity.compare w left right a).Installed M G cmp Fin.elim0 (U 0))
    (doneRow : M.code done = .accept) (c : Config w pc r) (m : Memory w)
    (old new : Fin a → Bool) (entry : c.pc=T 0) (tag : m phaseAddr.val = (ph.tag : Word w))
    (width : 7 ≤ 2^w) (leftFit : left+a < 2^w) (rightFit : right+a < 2^w)
    (lo : ∀ i, m (left+i.val) = TickBitRelation.bitWord w (old i))
    (hi : ∀ i, m (right+i.val) = TickBitRelation.bitWord w (new i))
    (passScan : ph = .scan → ∀ d : Config w pc r, d.pc=scan → Returns field M.program timeScan d m vScan)
    (passEval : ph = .evaluate → ∀ d : Config w pc r, d.pc=evaluation → Returns field M.program timeEval d m vEval) :
    Returns field M.program (17+6*a+max timeScan timeEval) c m
      (if ph=.scan then vScan else if old=new then (if ph=.evaluate then vEval else 1) else 0) := by
  obtain ⟨b,bpc,_,_,_,first⟩ := TickMarkerSwitch.advance_on M T R phaseAddr
    (Phase.scan.tag : Word w) scan (G (TickIdentity.compare w left right a).first) testRows c m entry
  simp only [tag,tag_eq ph .scan width] at bpc
  by_cases active : ph = .scan
  · rw [ite_eq_left active] at bpc ⊢
    exact ((passScan active b bpc).prefix first).later (by omega)
  · rw [ite_eq_right active] at bpc ⊢
    obtain ⟨d,dpc,guarded⟩ := TickChunkPreserve.mass_block field M left right G cmp Fin.elim0
      (U 0) chunkRows b m bpc leftFit rightFit old new (by omega) lo hi
    obtain ⟨f,fpc,_,_,_,last⟩ := TickMarkerSwitch.advance_on M U R phaseAddr
      (Phase.evaluate.tag : Word w) evaluation done lastRows d m dpc
    simp only [tag,tag_eq ph .evaluate width] at fpc
    have rest : Returns field M.program (4+(timeEval+1)) d m
        (if ph=.evaluate then vEval else 1) := by
      by_cases weight : ph=.evaluate
      · rw [ite_eq_left weight] at fpc ⊢
        exact ((passEval weight f fpc).later (Nat.le_succ _)).prefix last
      · rw [ite_eq_right weight] at fpc ⊢
        exact ((TickFuel.accept M f m (by rw [fpc]; exact doneRow)).later (by omega : 1 ≤ timeEval+1)).prefix last
    have guard : ∀ n, mass field M.program (n+(8+6*a)) b m =
        if old=new then mass field M.program n d m else 0 := by
      simpa only [Nat.add_assoc] using guarded
    exact (Returns.prefix first (Returns.guard (old=new) guard rest)).later (by omega)


end ThreeFlat.RAM.TickHistoryCore

end OAI
