import OAI.ThreeFlat.RAM.TickMountedPins
import OAI.ThreeFlat.RAM.HistoryFieldSeed
import OAI.ThreeFlat.RAM.TickClearInterpreter
import OAI.ThreeFlat.RAM.TickGenerateTable

namespace OAI
/-! # Evaluating a compiled slot directly on the mounted physical tick pins -/

namespace ThreeFlat.RAM.TickWeightedSlot

open Computability.VPVNP.BurstRAM PrivateRAM BitLayout Contraction HistoryFactors DescriptorExpr
open NativeRelocate
open scoped Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {w p pc r k : ℕ}

omit [Fintype F] [Field F] in
/-- All preprocessing scratch lies above the low pin and hidden-bit frame.
The original tape occupies exactly the two literals and all exposed pins. -/
theorem mounted_sources (N : BitNetwork F p) (pin : Fin p → Bool) (input : Memory w)
    (frame : ∀ i < cellsBase p N.internal, input i = TickMountedPins.memory pin i) :
    ∀ s : BitSource N.internal p, input (sourceAddress s) = bitWord w (s.read (fun _ => false) pin) := by
  have li := TickMountedPins.memory_constants (w:=w) pin
  apply HistoryFieldSeed.source_words
  · exact (frame 0 (by simp [cellsBase,hiddenBase])).trans li.1
  · exact (frame 1 (by simp [cellsBase,hiddenBase]; omega)).trans li.2
  · intro j
    exact (frame _ (by have := j.isLt; unfold cellsBase hiddenBase; omega)).trans
      (TickMountedPins.memory_at pin j)
  · intro j
    exact (frame _ (by have := j.isLt; unfold cellsBase; omega)).trans
      (TickMountedPins.memory_hidden pin j.val)

/-- The fixed field-multiplication ROM, 36-register clear and weighted
evaluator operate in the same native machine. The compact source/LUT rows
can vary with the history, while the interpreter pins use the original tick directly. -/
theorem mass_slot (M : Machine w pc r k) (N : BitNetwork F p) (fit : Fits N w) (L : Library N)
    («meta» lut : ℕ) (hm : footprint N ≤ «meta») (hl : footprint N ≤ lut)
    (bm : «meta»+4*N.cells ≤ 2^w) (bl : lut+8*L.count ≤ 2^w) (space : footprint N < 2^w)
    (pin : Fin p → Bool) (input : Memory w) (c : Config w pc r)
    (stored : Stores N L (codec N fit) «meta» lut input)
    (frame : ∀ a < cellsBase p N.internal, input a = TickMountedPins.memory pin a)
    (genPC : Fin ((HistoryFieldSeed.fieldExpr (K:=k) (codec N fit) (mulBase p N.internal N.cells)).labels+6) → Fin pc)
    (genReg : Fin (4+(HistoryFieldSeed.fieldExpr (K:=k) (codec N fit) (mulBase p N.internal N.cells)).binds) ↪ Fin r)
    (clearPC : Fin 37 → Fin pc) (runPC : Fin 108 ↪ Fin pc) (runReg : Fin 36 ↪ Fin r) (pub : Fin 7 → Fin k)
    (genROM : ∀ i, M.code (genPC i) = TickGenerateTable.emit
      (HistoryFieldSeed.fieldExpr (codec N fit) (mulBase p N.internal N.cells))
      (mulBase p N.internal N.cells : Word w) (footprint N : Word w) genPC genReg (clearPC 0) i)
    (clearROM : ∀ i : Fin 36, M.code (clearPC i.castSucc) = TickClearFrame.row clearPC runReg i)
    (toEval : clearPC (Fin.last 36) = runPC (interpreter p N.internal N.cells «meta» lut (F:=F) fit).entry)
    (evalROM : ∀ i, M.code (runPC i) = relocate runPC runReg pub
       ((interpreter p N.internal N.cells «meta» lut (F:=F) fit).code i))
    (par : ∀ i, M.publicData (pub i) = (interpreter p N.internal N.cells «meta» lut (F:=F) fit).publicData i)
    (entry : c.pc = TickGenerateTable.driver
       (HistoryFieldSeed.fieldExpr (codec N fit) (mulBase p N.internal N.cells)) genPC 0) :
    let q := Fintype.card F
    ∃ t ≤ 53+(q*q)*(6*(q*q)+10)+5*N.internal+550*N.cells, ∀ extra,
      mass (codec N fit) M.program (extra+t) c input = N.eval pin := by
  let b := mulBase p N.internal N.cells
  let q := Fintype.card F
  let code := codec N fit
  let e := HistoryFieldSeed.fieldExpr (K:=k) code b
  have bounds : b+q*q = footprint N := rfl
  have fb : (b : Word w).val = b := Fin.val_cast_of_lt (by omega)
  have fe : (footprint N : Word w).val = footprint N := Fin.val_cast_of_lt space
  obtain ⟨s,hs,out,hout,run⟩ := TickGenerateTable.generate e M (b : Word w) (footprint N : Word w)
    genPC genReg (clearPC 0) genROM (q*q) (by rw [fb,fe,bounds])
    (BitLayout.memory N code pin (fun _ => false)) c input entry (by
      intro x mem lo hi _
      rw [fb] at lo
      rw [fe] at hi
      exact PhysicalFieldTable.atAddress_memory N code pin (fun _ => false) (fun _ => 0)
        M.publicData mem (fun (_ : Fin 1) => x) (.literal (b : Word w)) (.result 0) x.val lo hi
        space.le rfl (Fin.ext (Nat.mod_eq_of_lt x.isLt).symm))
  rw [fb] at run
  change advance M.program s c input = some (out,HistoryFieldSeed.seeded N code pin input) at run
  refine ⟨s+49+5*N.internal+550*N.cells,?_,?_⟩
  · have cost := HistoryFieldSeed.fieldExpr_steps (K:=k) code b
    change e.steps = 6*(q*q)+7 at cost
    rw [cost] at hs
    convert Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hs 49) (5*N.internal)) (550*N.cells) using 1; ring
  · intro extra
    rw [show extra+(s+49+5*N.internal+550*N.cells) = (extra+49+5*N.internal+550*N.cells)+s by omega,
      mass_of_advance code M.program run]
    apply mass_clear_interpreter clearPC runPC runReg pub M N fit L «meta» lut
      (by omega) (by omega) bm bl _ (HistoryFieldSeed.stores_seeded N L code pin input hm hl stored)
      pin (fun _ => false) _ clearROM toEval evalROM par out hout extra
    exact HistoryFieldSeed.outside_field N code pin input (mounted_sources N pin input frame)

end ThreeFlat.RAM.TickWeightedSlot

end OAI
