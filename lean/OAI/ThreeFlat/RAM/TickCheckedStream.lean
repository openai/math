import OAI.ThreeFlat.RAM.TickGenerateTable
import OAI.ThreeFlat.RAM.TickCheckSetup
import OAI.ThreeFlat.RAM.TickRequestStream
import OAI.ThreeFlat.RAM.TickBitContinue

namespace OAI
/-! # Generating and checking the native records for a physical bit vector -/

namespace ThreeFlat.RAM.TickCheckedStream

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickAuxiliary TickBitRelation ChunkRequests
open scoped Classical Fin.CommRing

variable {w p r k a : ℕ} {F : Type*} [Semiring F]

/-- The supplied one-word native term computes the guard for each bit.
Generated records, register setup and the native checker all use one machine.
On success it enters the caller's continuation at a concrete state; failure has zero weight. -/
theorem mass_generated (field : FieldCode F w) (M : Machine w p r k)
    (e : Term w k 1) (rule : ℕ → Rule) (start : ℕ) (old new : Word w)
    (oldBits newBits : Fin a → Bool) (c : Config w p r) (m : Memory w)
    (fit : 64 ≤ 2^w) (endFit : start+8*a < 2^w)
    (genPC : Fin ((TickRequestStream.program start e).labels+6) → Fin p)
    (genRegs : Fin (4+(TickRequestStream.program start e).binds) ↪ Fin r)
    (setup : Fin 7 → Fin p) (R : Registers w k r) (L : Labels w k p)
    (zeroReg : Fin r) (test bad next : Fin p)
    (genROM : ∀ i, M.code (genPC i) = TickGenerateTable.emit (TickRequestStream.program start e)
      (start : Word w) (start+8*a : ℕ) genPC genRegs (setup 0) i)
    (setupROM : ∀ i, M.code (setup i) = TickCheckSetup.emit setup R.slot
      (TickCheckSetup.values (start : Word w) old new (start+8*a : ℕ)) L.guard i)
    (checkROM : ContinueInstalled M R L zeroReg test bad next)
    (entry : c.pc = TickGenerateTable.driver (TickRequestStream.program start e) genPC 0)
    (correct : ∀ (mm : Memory w), DescriptorScan.agreesOutside start (start+8*a) mm m →
      ∀ i : Fin a, e.eval M.publicData mm (fun _ => (i.val : Word w)) = ((rule i.val).tag : Word w))
    (oldOutside : ∀ i : Fin a, (old+(i.val : Word w)).val < start)
    (newOutside : ∀ i : Fin a, (new+(i.val : Word w)).val < start)
    (old_ok : ∀ i : Fin a, bitAt m old (i.val : Word w) = bitWord w (oldBits i))
    (new_ok : ∀ i : Fin a, bitAt m new (i.val : Word w) = bitWord w (newBits i)) :
    let saved := fillSegment start (8*a) (TickRequestStream.dataWord start rule) m
    ∃ t ≤ 14+8*a*((TickRequestStream.program start e).steps+3)+a*122,
      ∃ out : Config w p r, out.pc = next ∧
      ∀ fuel, mass field M.program (fuel+t) c m =
        if ∀ i : Fin a, (rule i.val).holds (oldBits i) (newBits i)
        then mass field M.program fuel out saved else 0 := by
  dsimp only
  let expr := TickRequestStream.program start e
  let vals := TickCheckSetup.values (start : Word w) old new (start+8*a : ℕ)
  let saved := fillSegment start (8*a) (TickRequestStream.dataWord start rule) m
  have fs : (start : Word w).val = start := Fin.val_cast_of_lt (by omega)
  have fe : ((start+8*a : ℕ) : Word w).val = start+8*a := Fin.val_cast_of_lt endFit
  obtain ⟨s,hs,c₁,h₁,exec₁⟩ := TickGenerateTable.generate expr M (start : Word w)
    (start+8*a : ℕ) genPC genRegs (setup 0) genROM (8*a) (by rw [fs,fe])
    (TickRequestStream.dataWord start rule) c m entry (by
      intro x mm hlow high frame
      rw [fs] at hlow frame
      rw [fe] at high frame
      exact TickRequestStream.program_eval start rule e M.publicData mm x hlow high fit (correct mm frame))
  rw [fs] at exec₁
  let c₂ := TickCheckSetup.loaded setup R.slot vals L.guard c₁
  have exec₂ := TickCheckSetup.advance_setup M setup R.slot vals L.guard setupROM c₁ saved h₁
  have both := advance_trans exec₁ exec₂
  have reg (i : Fin 7) : c₂.reg (R.slot i) = vals i := TickCheckSetup.loaded_reg ..
  let out := (scan M.publicData R L (a*2) c₂ saved).1.put next zeroReg 0
  refine ⟨s+7+(3+a*122),by dsimp [expr] at hs; omega,out,rfl,?_⟩
  intro fuel
  have zeroOne : (1 : Word w) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    have o : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (show (1 : ℕ) < 2^w by omega)
    simp only [o,Fin.val_zero] at this
    omega
  have read (i : Fin a) (d : Fin 8) :
      saved (start+8*i.val+d.val) = (paddedRequest (rule i.val)
          (TickAuxRequestWord.slot d) (i.val : Word w)).column (TickAuxRequestWord.index d) := by
    have hi := i.isLt
    have hd := d.isLt
    simp only [saved,fillSegment, ite_eq_left (show start ≤ start+8*i.val+d.val ∧
      start+8*i.val+d.val < start+8*a by omega)]
    exact TickRequestStream.dataWord_at start rule i.val d
  have tail := mass_range_continue field M R L zeroReg test bad next checkROM
    (fun i : Fin a => rule i.val) fuel c₂ saved oldBits newBits (by omega) rfl
    (by rw [reg]; exact Nat.mod_eq_of_lt (show (4 : ℕ) < 2^w by omega))
    (by rw [reg,reg]; change (start : Word w).val+_ = ((start+8*a : ℕ) : Word w).val
        rw [fs,fe]; omega)
    (by rw [reg]; rfl) (by rw [reg]; exact zeroOne)
    (by intro i d; rw [reg]; change saved ((start : Word w).val+8*i.val+d.val) = _
        rw [fs]; exact read i d)
    (by intro i; rw [reg]; change saved (old+(i.val : Word w)).val = _
        dsimp only [saved,fillSegment]
        rw [ite_eq_right (fun covers => (Nat.not_le_of_lt (oldOutside i)) covers.1)]
        exact old_ok i)
    (by intro i; rw [reg]; change saved (new+(i.val : Word w)).val = _
        dsimp only [saved,fillSegment]
        rw [ite_eq_right (fun covers => (Nat.not_le_of_lt (newOutside i)) covers.1)]
        exact new_ok i)
  have head := mass_of_advance field M.program both (fuel+3+a*122)
  rw [show fuel+(s+7+(3+a*122)) = (fuel+3+a*122)+(s+7) by omega]
  exact head.trans tail

end ThreeFlat.RAM.TickCheckedStream

end OAI
