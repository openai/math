import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.TickAuxRequestROM
import OAI.ThreeFlat.RAM.TickCheckedStream

namespace OAI
/-! # Generating and executing auxiliary comparison records from the runtime header -/

namespace ThreeFlat.RAM.TickAuxRequestGen

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickChronology Diagonal.TickAuxiliary
open ChunkRequests TickBitRelation
open scoped Fin.CommRing

variable {w k : ℕ}

theorem row_eval {a : ℕ} (A : Layout a) (p : Phase) (run : Bool) (i : Fin a)
    (addr : Fin 4 → Word w) (size : a < 2^w) (fit : 7 ≤ 2^w) (par : Fin k → Word w)
    (m : Memory w) (h : ∀ j, m (addr j).val = header A p run j) :
    (row addr).eval par m (fun _ => (i.val : Word w)) = ((A.rule p run i.val).tag : Word w) := by
  unfold row
  rw [Term.eval_instantiate]
  convert TickGuardRule.program_eval A p run i size fit par m using 2
  funext j
  fin_cases j <;> simp [Term.eval,h,header,TickGuardRule.input]

open scoped Classical

/-- A fixed native table computes the entire auxiliary endpoint indicator,
including the marker and all padding. Cost is linear in physical width.
The branch choice and the two dynamic endpoints come from constant header addresses. -/
theorem mass_aux {a pc regs : ℕ} {F : Type*} [Semiring F]
    (field : FieldCode F w) (M : Machine w pc regs k) (A : Layout a) (p : Phase) (run : Bool)
    (addr : Fin 4 → Word w) (start : ℕ) (old new : Word w) (x y : Fin a → Bool)
    (c : Config w pc regs) (m : Memory w) (fit : 64 ≤ 2^w) (endFit : start+8*a < 2^w)
    (genPC : Fin ((TickRequestStream.program start (row (k:=k) addr)).labels+6) → Fin pc)
    (genRegs : Fin (4+(TickRequestStream.program start (row (k:=k) addr)).binds) ↪ Fin regs)
    (setup : Fin 7 → Fin pc) (R : Registers w k regs) (L : ChunkRequests.Labels w k pc)
    (zeroReg : Fin regs) (test bad next : Fin pc)
    (genROM : ∀ i, M.code (genPC i) = TickGenerateTable.emit (TickRequestStream.program start (row addr))
      (start : Word w) (start+8*a : ℕ) genPC genRegs (setup 0) i)
    (setupROM : ∀ i, M.code (setup i) = TickCheckSetup.emit setup R.slot
      (TickCheckSetup.values (start : Word w) old new (start+8*a : ℕ)) L.guard i)
    (checkROM : ContinueInstalled M R L zeroReg test bad next)
    (entry : c.pc = TickGenerateTable.driver (TickRequestStream.program start (row (k:=k) addr)) genPC 0)
    (headerSafe : ∀ j, (addr j).val < start)
    (hdr : ∀ j, m (addr j).val = header A p run j)
    (oldOutside : ∀ i : Fin a, (old+(i.val : Word w)).val < start)
    (newOutside : ∀ i : Fin a, (new+(i.val : Word w)).val < start)
    (old_ok : ∀ i : Fin a, bitAt m old (i.val : Word w) = bitWord w (x i))
    (new_ok : ∀ i : Fin a, bitAt m new (i.val : Word w) = bitWord w (y i)) :
    let saved := fillSegment start (8*a) (TickRequestStream.dataWord start (A.rule p run)) m
    ∃ t ≤ 14+a*5082, ∃ out : Config w pc regs, out.pc = next ∧
      ∀ fuel, mass field M.program (fuel+t) c m =
        if A.accepts p run x y then mass field M.program fuel out saved else 0 := by
  obtain ⟨t,ht,out,hout,eq⟩ := TickCheckedStream.mass_generated field M (row addr) (A.rule p run)
    start old new x y c m fit endFit genPC genRegs setup R L zeroReg test bad next genROM setupROM
    checkROM entry (by
      intro mm frame i
      exact row_eval A p run i addr (by omega) (by omega) M.publicData mm
        (fun j => (frame _ (Or.inl (headerSafe j))).trans (hdr j)))
    oldOutside newOutside old_ok new_ok
  refine ⟨t,ht.trans ?_,out,hout,?_⟩
  swap
  · intro fuel
    unfold Layout.accepts
    by_cases accepted : ∀ i : Fin a, (A.rule p run i.val).holds (x i) (y i)
    · simpa only [ite_eq_left accepted] using eq fuel
    · simpa only [ite_eq_right accepted] using eq fuel
  have s := TickRequestStream.program_binds start (row (k:=k) addr)
  have r := row_binds (k:=k) addr
  have n : (TickRequestStream.program start (row (k:=k) addr)).steps+3 ≤ 620 := by
    rw [Term.steps_eq]
    omega
  have wbound := Nat.mul_le_mul_left (8*a) n
  omega


end ThreeFlat.RAM.TickAuxRequestGen

end OAI
