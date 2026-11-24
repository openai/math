import OAI.Computability.VPVNP.RAMTapePublicExprArithmetic

/-! # Register allocation for nested public expressions

An expression writes its result at its base register and uses only registers
above that base for intermediate words. Computing a right operand one position
higher therefore retains the already computed left operand.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicExprMachine

open BurstRAM PrivateRAM LiveProgram

variable {r : ℕ}

/-- Interpret a natural base address in the finite bank of one more than the supplied register
bound. -/
def addr (r base : ℕ) : Fin (r+1) := Fin.ofNat (r+1) base

theorem addr_val {base : ℕ} (hb : base ≤ r) : (addr r base).val = base :=
  Nat.mod_eq_of_lt (by omega)

/-- Arithmetic bank with the bounded register file and four public geometry words. -/
abbrev BankPort (r : ℕ) := ISA.Port (r+1) 4

/-- The routine writes the packed natural result at its base within the step budget, preserving
all lower registers, public words, persistent state, and log. -/
def Computes (g : Geometry) (r base value steps : ℕ) (routine : FiniteRoutine (BankPort r)) : Prop :=
  ∀ (persist : Word g.w) (rs : Fin (r+1) → Word g.w) (log : WriteLog g.w),
    ∃ t ≤ steps, ∃ out : Fin (r+1) → Word g.w,
      routine.Runs t (ISA.bank (geometryWords g) persist rs log) (ISA.bank (geometryWords g) persist out log) ∧
      out (addr r base) = packed g.w value ∧ ∀ i : Fin (r+1), i.val < base → out i = rs i

theorem Computes.mono {g : Geometry} {base v m n : ℕ} {code : FiniteRoutine (BankPort r)}
    (h : Computes g r base v m code) (hm : m ≤ n) : Computes g r base v n code := by
  intro p rs log
  obtain ⟨t, ht, rest⟩ := h p rs log
  exact ⟨t, ht.trans hm, rest⟩

private theorem below_ne {base : ℕ} (hb : base ≤ r) {i : Fin (r+1)} (hi : i.val < base) :
    i ≠ addr r base := fun he => by rw [he, addr_val hb] at hi; omega

theorem literal_computes (g : Geometry) (base n : ℕ) (hb : base ≤ r) :
    Computes g r base n (8*g.w+3) (ISA.loadLiteral n (addr r base)) := by
  intro p rs log
  exact ⟨_, le_rfl, _, ISA.loadLiteral_run .., Function.update_self ..,
    fun i hi => Function.update_of_ne (below_ne hb hi) ..⟩

theorem load_computes (g : Geometry) (base : ℕ) (i : Fin 4) (hb : base ≤ r) :
    Computes g r base (geometryNat g i) (8*g.w+3) (load (addr r base) i) := by
  intro p rs log
  exact ⟨_, le_rfl, _, load_runs .., Function.update_self ..,
    fun j hj => Function.update_of_ne (below_ne hb hj) ..⟩

/-- Sequence the two operand routines, then apply the binary word operation to the base
register and its successor. -/
def combine (op : Arithmetic) (base : ℕ) (a b : FiniteRoutine (BankPort r)) : FiniteRoutine (BankPort r) :=
  (a.followedBy b).followedBy (op.code (addr r base) (addr r base) (addr r (base+1)))

theorem combine_computes (g : Geometry) (op : Arithmetic) {base x y u v : ℕ}
    {a b : FiniteRoutine (BankPort r)} (hb : base+1 ≤ r)
    (hx : x < 2^g.w) (hy : y < 2^g.w)
    (ha : Computes g r base x u a) (hc : Computes g r (base+1) y v b) :
    Computes g r base (op.eval x y) (u+v+150*(g.w+1)^2) (combine op base a b) := by
  intro p rs log
  obtain ⟨t, ht, l, first, hl, kl⟩ := ha p rs log
  obtain ⟨s, hs, z, second, hz, kz⟩ := hc p l log
  obtain ⟨k, hk, applyOp⟩ := op.runs (addr r base) (addr r base) (addr r (base+1)) (geometryWords g) p z log
  have old : z (addr r base) = packed g.w x := (kz _ (by rw [addr_val (by omega)]; omega)).trans hl
  rw [old, hz, packed_val hx, packed_val hy] at applyOp
  refine ⟨_, Nat.add_le_add (Nat.add_le_add ht hs) hk, _, (first.followedBy second).followedBy applyOp,
    Function.update_self .., ?_⟩
  intro i hi
  rw [Function.update_of_ne (below_ne (by omega) hi), kz i (by omega), kl i hi]

/-- Evaluate the operand, then run the constant operation with the next register as scratch. -/
def constant (op : ConstantOp) (base : ℕ) (a : FiniteRoutine (BankPort r)) : FiniteRoutine (BankPort r) :=
  a.followedBy (op.code (addr r base) (addr r (base+1)))

theorem constant_computes (g : Geometry) (op : ConstantOp) {base x u : ℕ}
    {a : FiniteRoutine (BankPort r)} (hb : base+1 ≤ r)
    (hx : x < 2^g.w) (hlit : op.literal < 2^g.w) (hout : op.eval x < 2^g.w)
    (ha : Computes g r base x u a) :
    Computes g r base (op.eval x) (u+150*(g.w+1)^2) (constant op base a) := by
  intro p rs log
  obtain ⟨t, ht, l, first, hl, keep⟩ := ha p rs log
  have val : (l (addr r base)).val = x := by rw [hl, packed_val hx]
  have hdst : addr r base ≠ addr r (base+1) :=
    below_ne hb (by rw [addr_val (by omega)]; omega)
  obtain ⟨k,hk,hr⟩ := op.runs (addr r base) (addr r (base+1)) hdst (geometryWords g) p l log
    hlit (val ▸ hout)
  rw [val] at hr
  refine ⟨_, Nat.add_le_add ht hk, _, first.followedBy hr, Function.update_self .., ?_⟩
  intro i hi
  rw [Function.update_of_ne (below_ne (by omega) hi), Function.update_of_ne (below_ne hb (by omega)), keep i hi]

end RAMTape.PublicExprMachine

end VPVNP
end Computability
end OAI
