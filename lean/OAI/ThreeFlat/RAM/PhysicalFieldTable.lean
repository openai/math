import OAI.ThreeFlat.RAM.LiteralTable
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Native generation of the field multiplication table -/

namespace ThreeFlat.RAM.PhysicalFieldTable

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr BitLayout
open scoped Fin.CommRing

variable {F : Type*} [Fintype F] [Semiring F] {w k n p : ℕ}

/-- The field table uses the row-major order of the two field ordinals. -/
noncomputable def entry (code : FieldCode F w) (i : ℕ) : Word w :=
  if hi : i < Fintype.card F * Fintype.card F then
    let q := Fintype.card F
    let a : Fin q := ⟨i/q,(Nat.div_lt_iff_lt_mul Fintype.card_pos).2 hi⟩
    let b : Fin q := ⟨i%q,Nat.mod_lt _ Fintype.card_pos⟩
    code.encode ((Fintype.equivFin F).symm a * (Fintype.equivFin F).symm b)
  else 0

/-- The program contains a constant pair of literals and an equality branch per entry. -/
noncomputable def term (code : FieldCode F w) : Term w k 1 :=
  LiteralTable.lookup (entry code) (Fintype.card F * Fintype.card F)

@[simp] theorem term_binds (code : FieldCode F w) :
    (term (k := k) code).binds = 3*(Fintype.card F * Fintype.card F)+1 :=
  LiteralTable.lookup_binds ..

theorem term_eval (code : FieldCode F w) (i : ℕ) (hi : i < Fintype.card F * Fintype.card F)
    (fit : Fintype.card F * Fintype.card F ≤ 2^w)
    (params : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w) (arg : vs 0 = (i : Word w)) :
    (term code).eval params mem vs = entry code i := LiteralTable.lookup_eval _ _ _ hi fit _ _ _ arg

/-- Any ordinal in the bounded field tail names the same coefficient as the
contraction interpreter's official memory image. -/
theorem read_entry (N : BitNetwork F p) (code : FieldCode F w) (pin : Fin p → Bool)
    (hidden : Fin N.internal → Bool) (tail : Memory w) (i : ℕ)
    (hi : i < Fintype.card F * Fintype.card F) :
    memoryWithTail tail N code pin hidden (mulBase p N.internal N.cells+i) = entry code i := by
  let q := Fintype.card F
  let a : Fin q := ⟨i/q,(Nat.div_lt_iff_lt_mul Fintype.card_pos).2 hi⟩
  let b : Fin q := ⟨i%q,Nat.mod_lt _ Fintype.card_pos⟩
  have haddr : mulBase p N.internal N.cells + q*a.val + b.val = mulBase p N.internal N.cells+i := by
    rw [Nat.add_assoc]
    exact congrArg (mulBase p N.internal N.cells + ·) (Nat.div_add_mod i q)
  have h := read_product N code pin hidden ((Fintype.equivFin F).symm a) ((Fintype.equivFin F).symm b) tail
  simp only [Equiv.apply_symm_apply] at h
  rw [← haddr]
  simpa only [entry,dite_eq_left hi] using h

/-- Read the product code at the absolute address `address`, using the
native subtraction instruction to form its offset from `base`. -/
noncomputable def atAddress (code : FieldCode F w) (base address : Term w k n) : Term w k n :=
  LiteralTable.atIndex (entry code) (Fintype.card F * Fintype.card F) (.binary .sub address base)

@[simp] theorem atAddress_binds (code : FieldCode F w) (base address : Term w k n) :
    (atAddress code base address).binds =
      3*(Fintype.card F * Fintype.card F)+1 + (address.binds + base.binds + 1) := by
  simp [atAddress,Term.binary,Term.binds,Nat.add_assoc]

theorem atAddress_eval (code : FieldCode F w) (base address : Term w k n)
    (params : Fin k → Word w) (mem : Memory w) (vs : Fin n → Word w)
    (start i : ℕ) (hi : i < Fintype.card F * Fintype.card F)
    (fit : Fintype.card F * Fintype.card F ≤ 2^w)
    (hb : base.eval params mem vs = (start : Word w))
    (ha : address.eval params mem vs = ((start+i : ℕ) : Word w)) :
    (atAddress code base address).eval params mem vs = entry code i := by
  apply LiteralTable.atIndex_eval _ _ _ hi fit
  simp [Term.eval_binary,ha,hb,BinaryOp.eval,Nat.cast_add]

/-- The native expression agrees word-for-word with the complete multiplication-table
segment at every address between `mulBase` and `footprint`. -/
theorem atAddress_memory (N : BitNetwork F p) (code : FieldCode F w) (pin : Fin p → Bool)
    (hidden : Fin N.internal → Bool) (tail : Memory w) (params : Fin k → Word w)
    (mem : Memory w) (vs : Fin n → Word w) (base address : Term w k n) (a : ℕ)
    (lo : mulBase p N.internal N.cells ≤ a) (hi : a < footprint N) (fit : footprint N ≤ 2^w)
    (hb : base.eval params mem vs = (mulBase p N.internal N.cells : Word w))
    (ha : address.eval params mem vs = (a : Word w)) :
    (atAddress code base address).eval params mem vs = memoryWithTail tail N code pin hidden a := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le lo
  unfold footprint at hi fit
  have hr : i < Fintype.card F * Fintype.card F := by omega
  exact (atAddress_eval code base address params mem vs _ i hr (by omega) hb ha).trans
    (read_entry N code pin hidden tail i hr).symm

end ThreeFlat.RAM.PhysicalFieldTable

end OAI
