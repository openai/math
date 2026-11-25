import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

namespace OAI
/-! # One ROM for all dyadic stable-compactor templates up to a public exponent

The `m`th template starts at `base + m*page B C`. Each row reserves exactly
`C` words and unused row slots read as zero.
-/

namespace ThreeFlat.RAM.StableCompactROMPool

open scoped Fin.NatCast

def rows (B : ℕ) := 32000*(B+1)^3
def page (B C : ℕ) := rows B*C
def size (B C : ℕ) := (B+1)*page B C
def address (B C m i t : ℕ) := m*page B C+i*C+t

theorem size_eq (B C : ℕ) : size B C = 32000*C*(B+1)^4 := by
  unfold size page rows
  ring

theorem size_le_of_degree {B C w K : ℕ} (h : B+1 ≤ K*(w+1)^10) :
    size B C ≤ 32000*C*K^4*(w+1)^40 := by
  rw [size_eq]
  calc
    _ ≤ 32000*C*(K*(w+1)^10)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = _ := by rw [mul_pow,←pow_mul]; ring

def index (B C : ℕ) : Fin (B+1) × (Fin (rows B) × Fin C) ≃ Fin (size B C) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

@[simp] theorem index_val (B C : ℕ) (m : Fin (B+1)) (i : Fin (rows B)) (t : Fin C) :
    (index B C (m,i,t)).val = address B C m.val i.val t.val := by
  change (t.val+C*i.val)+page B C*m.val = _
  unfold address
  ring

variable {B C : ℕ} (count : ℕ → ℕ) (cap : ∀ m : Fin (B+1), count m ≤ rows m)

include cap in
private theorem fits (m : Fin (B+1)) : count m ≤ rows B :=
  (cap m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.le_of_lt_succ m.isLt)) 3))

/-- Every live row word has its own physical cell, including rows from different templates. -/
def place : (Σ m : Fin (B+1), Fin (count m) × Fin C) ↪ Fin (size B C) where
  toFun q := index B C (q.1,q.2.1.castLE (fits count cap q.1),q.2.2)
  inj' := by
    rintro ⟨m,i,t⟩ ⟨m',i',t'⟩ same
    have pairs := (index B C).injective same
    obtain rfl : m = m' := congrArg Prod.fst pairs
    obtain rfl : i = i' := Fin.ext (congrArg (fun p : Fin (B+1) × (Fin (rows B) × Fin C) => p.2.1.val) pairs)
    obtain rfl : t = t' := congrArg (fun p : Fin (B+1) × (Fin (rows B) × Fin C) => p.2.2) pairs
    rfl

@[simp] theorem place_val (m : Fin (B+1)) (i : Fin (count m)) (t : Fin C) :
    ((place count cap) ⟨m,i,t⟩).val = address B C m i t := index_val ..

include cap in
theorem address_lt (m : Fin (B+1)) (i : Fin (count m)) (t : Fin C) :
    address B C m i t < size B C := by
  rw [←place_val count cap m i t]
  exact ((place count cap) ⟨m,i,t⟩).isLt

/-- Interpret a ROM word index by unflattening its page, row, and field.
Rows between the actual template height and its fixed-stride allocation read as zero. -/
def data {α : Type*} [Zero α] (B C : ℕ) (count : ℕ → ℕ)
    (field : ∀ m, Fin (count m) → Fin C → α) (z : Fin (size B C)) : α :=
  let q := (index B C).symm z
  if hi : q.2.1.val < count q.1 then field q.1 ⟨q.2.1.val,hi⟩ q.2.2 else 0

@[simp] theorem data_place {α : Type*} [Zero α] (field : ∀ m, Fin (count m) → Fin C → α)
    (m : Fin (B+1)) (i : Fin (count m)) (t : Fin C) :
    data B C count field (place count cap ⟨m,i,t⟩) = field m i t := by
  let readField (q : Fin (B+1) × (Fin (rows B) × Fin C)) : α :=
    if hi : q.2.1.val < count q.1 then field q.1 ⟨q.2.1.val,hi⟩ q.2.2 else 0
  change readField ((index B C).symm ((index B C) (m,i.castLE (fits count cap m),t))) = _
  rw [Equiv.symm_apply_apply]
  change (if h : i.val < count m then field m ⟨i.val,h⟩ t else 0) = _
  exact dite_eq_left i.isLt

/-- Place the pool at a natural base in the machine's memory, retaining its other words. -/
def install {α : Type*} (base N : ℕ) (pool : Fin N → α) (old : ℕ → α) (x : ℕ) : α :=
  if hx : base ≤ x ∧ x < base+N then pool ⟨x-base,by omega⟩ else old x

theorem install_at {α : Type*} {N : ℕ} (base : ℕ) (pool : Fin N → α) (old : ℕ → α) (i : Fin N) :
    install base N pool old (base+i.val) = pool i := by
  simp [install,i.isLt]

theorem install_outside {α : Type*} {N : ℕ} (base : ℕ) (pool : Fin N → α) (old : ℕ → α) {x : ℕ}
    (outside : x < base ∨ base+N ≤ x) : install base N pool old x = old x :=
  dite_eq_right (by omega)

include cap in
/-- Reading the affine physical address fetches the specified template word. -/
theorem read {α : Type*} [Zero α] (field : ∀ m, Fin (count m) → Fin C → α)
    (base : ℕ) (old : ℕ → α) (m : Fin (B+1)) (i : Fin (count m)) (t : Fin C) :
    install base (size B C) (data B C count field) old (base+address B C m i t) = field m i t := by
  rw [←place_val count cap m i t,install_at,data_place]

include cap in
/-- A word-addressed machine performs the same lookup when the pool fits. -/
theorem read_word {w : ℕ} (field : ∀ m, Fin (count m) → Fin C → Fin (2^w))
    (base : ℕ) (old : ℕ → Fin (2^w)) (m : Fin (B+1)) (i : Fin (count m)) (t : Fin C)
    (room : base+size B C ≤ 2^w) :
    install base (size B C) (data B C count field) old
      (((base+address B C m i t : ℕ) : Fin (2^w)).val) = field m i t := by
  have small : base+address B C m i t < 2^w :=
    (Nat.add_lt_add_left (address_lt count cap m i t) base).trans_le room
  rw [Fin.val_cast_of_lt small,read count cap]

end ThreeFlat.RAM.StableCompactROMPool

end OAI
