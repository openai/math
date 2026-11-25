import OAI.ThreeFlat.MaterializeCells
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Installing the addressed rows in the evaluator's RAM

Each store has a word-sized address and writes one word. The first three
columns hold resolved source addresses and the remaining eight encode the
cell's coefficients. Private updates overwrite only those coefficients.
-/

namespace ThreeFlat.BitNetwork

open Computability.VPVNP.BurstRAM
open RAM RAM.BitLayout

variable {q w p g : ℕ} {F : Type*}

def rowLocation (base : ℕ) (a : RowAddress q) : ℕ :=
  base + 11 * a.1.val + (finSumFinEquiv a.2 : Fin 11).val

theorem rowLocation_range (base : ℕ) (a : RowAddress q) :
    base ≤ rowLocation base a ∧ rowLocation base a < base + 11*q := by
  have := a.1.isLt
  have := (finSumFinEquiv a.2 : Fin 11).isLt
  unfold rowLocation
  omega

theorem rowLocation_injective (base : ℕ) : Function.Injective (rowLocation (q := q) base) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change base + 11*i.val + (finSumFinEquiv a : Fin 11).val =
    base + 11*j.val + (finSumFinEquiv b : Fin 11).val at h
  have ha := (finSumFinEquiv a : Fin 11).isLt
  have hb := (finSumFinEquiv b : Fin 11).isLt
  have hi : i.val = j.val := by omega
  have hj : (finSumFinEquiv a : Fin 11).val = (finSumFinEquiv b : Fin 11).val := by omega
  exact Prod.ext (Fin.ext hi) (finSumFinEquiv.injective (Fin.ext hj))

theorem exists_rowLocation {base k : ℕ} (lo : base ≤ k) (hi : k < base + 11*q) :
    ∃ a : RowAddress q, rowLocation base a = k := by
  let i : Fin q := ⟨(k-base)/11, (Nat.div_lt_iff_lt_mul (by decide : 0 < 11)).mpr (by omega)⟩
  let j : Fin 11 := ⟨(k-base)%11, Nat.mod_lt _ (by decide)⟩
  refine ⟨(i, finSumFinEquiv.symm j), ?_⟩
  simp only [rowLocation, Equiv.apply_symm_apply, i, j]
  have := Nat.div_add_mod (k-base) 11
  omega

/-- The actual burst-RAM writes, in their chronological order. -/
def rowStores (base : ℕ) (xs : List (CellWrite q (Word w))) : List (Event w) :=
  xs.map fun e => .write (Fin.ofNat _ (rowLocation base e.1)) e.2

theorem rowStores_read (base : ℕ) (hfit : base + 11*q ≤ 2^w) (xs : List (CellWrite q (Word w)))
    (initial : Memory w) (a : RowAddress q) :
    after initial (rowStores base xs) (rowLocation base a) =
    replayWrites xs (fun j => initial (rowLocation base j)) a := by
  induction xs generalizing initial with
  | nil => rfl
  | cons e es ih =>
    have hw : rowLocation base e.1 % (2^w) = rowLocation base e.1 :=
      Nat.mod_eq_of_lt ((rowLocation_range base e.1).2.trans_le hfit)
    let next := writeMemory initial (Fin.ofNat _ (rowLocation base e.1)) e.2
    have pull : (fun j => next (rowLocation base j)) =
        Function.update (fun j => initial (rowLocation base j)) e.1 e.2 := by
      funext j
      by_cases he : j = e.1
      · subst j
        simp [next, writeMemory, hw]
      · have ne : rowLocation base j ≠ rowLocation base e.1 :=
          fun eq => he (rowLocation_injective base eq)
        simp only [next, writeMemory, Fin.val_ofNat, hw, ite_eq_right ne, Function.update_of_ne he]
    change after next (rowStores base es) (rowLocation base a) =
      replayWrites es (Function.update (fun j => initial (rowLocation base j)) e.1 e.2) a
    rw [ih, pull]

theorem rowStores_outside (base : ℕ) (hfit : base + 11*q ≤ 2^w) (xs : List (CellWrite q (Word w)))
    (initial : Memory w) (k : ℕ) (hk : k < base ∨ base + 11*q ≤ k) :
    after initial (rowStores base xs) k = initial k := by
  induction xs generalizing initial with
  | nil => rfl
  | cons e es ih =>
    have hr := rowLocation_range base e.1
    have hw : rowLocation base e.1 % (2^w) = rowLocation base e.1 :=
      Nat.mod_eq_of_lt (hr.2.trans_le hfit)
    have hne : k ≠ rowLocation base e.1 := by omega
    change after (writeMemory initial (Fin.ofNat _ _) e.2) (rowStores base es) k = _
    rw [ih]
    simp [writeMemory, hw, hne]

def sourceWords (N : BitNetwork F p) (w : ℕ) (i : Fin N.cells) (k : Fin 3) : Word w :=
  Fin.ofNat _ (sourceAddress (N.source i k))

private theorem key_bits_fin (i : Fin 8) : key (bits i.val) = i.val := by revert i; decide

theorem read_row_slot [Fintype F] [Semiring F] (N : BitNetwork F p) (code : FieldCode F w)
    (pins : Fin p → Bool) (h : Fin N.internal → Bool) (a : RowAddress N.cells) :
    memory N code pins h (rowLocation (cellsBase p N.internal) a) =
      cellRows (N.sourceWords w) N.table code.encode a := by
  rcases a with ⟨i,j|k⟩
  · exact read_wireAddress N code pins h i j
  · change memoryWithTail (fun _ => 0) N code pins h (cellsBase p N.internal + 11*i.val + (3+k.val)) =
      code.encode (N.table i (bits k.val))
    simpa only [key_bits_fin] using read_factor N code pins h i (bits k.val)

variable (N : BitNetwork F p) (c : ℕ) (connect : Fin c → Fin p → BitSource 0 g)
  (code : FieldCode F w) (updates : List (DirtyRow F (c*N.cells)))

/-- Populate the actual evaluator memory block from the common template and sparse overrides. -/
def repeatedStores : List (Event w) :=
  rowStores (cellsBase g (c*N.internal))
    (cellWritePlan (q := c*N.cells) ((N.repeated c connect updates).sourceWords w)
      (fun i => N.table (finProdFinEquiv.symm i).2) code.encode updates)

theorem repeatedStores_length : (N.repeatedStores c connect code updates).length =
    c*N.cells*11 + updates.length*8 := by
  simpa only [repeatedStores, rowStores, List.length_map] using
    cellWritePlan_length (q := c*N.cells) ((N.repeated c connect updates).sourceWords w)
      (fun i => N.table (finProdFinEquiv.symm i).2) code.encode updates

variable [fintypeF : Fintype F] [semiringF : Semiring F]
variable (pin : Fin g → Bool) (hidden : Fin (c*N.internal) → Bool)

/-- Pointwise agreement on every one of the eleven columns of every installed row. -/
theorem repeatedStores_read (fit : mulBase g (c*N.internal) (c*N.cells) ≤ 2^w)
    (initial : Memory w) (a : RowAddress (c*N.cells)) :
    after initial (N.repeatedStores c connect code updates) (rowLocation (cellsBase g (c*N.internal)) a) =
    memory (N.repeated c connect updates) code pin hidden (rowLocation (cellsBase g (c*N.internal)) a) := by
  let base := cellsBase g (c*N.internal)
  let wires : Fin (c*N.cells) → Fin 3 → Word w := (N.repeated c connect updates).sourceWords w
  let rows := fun i : Fin (c*N.cells) => N.table (finProdFinEquiv.symm i).2
  let xs := cellWritePlan wires rows code.encode updates
  have filled := congrFun (replay_cellWritePlan wires rows code.encode updates
    (fun j => initial (rowLocation base j))) a
  exact (rowStores_read base fit xs initial a).trans
    (filled.trans (read_row_slot (N.repeated c connect updates) code pin hidden a).symm)

/-- A row installation yields the complete dense memory, provided the disjoint
pin, hidden, constant and field-multiplication regions were already installed. -/
theorem repeatedStores_memory (fit : mulBase g (c*N.internal) (c*N.cells) ≤ 2^w)
    (initial : Memory w)
    (outside : ∀ k, k < cellsBase g (c*N.internal) ∨ mulBase g (c*N.internal) (c*N.cells) ≤ k →
      initial k = memory (N.repeated c connect updates) code pin hidden k) :
    after initial (N.repeatedStores c connect code updates) =
      memory (N.repeated c connect updates) code pin hidden := by
  funext k
  by_cases lo : k < cellsBase g (c*N.internal)
  · exact (rowStores_outside _ fit _ initial k (Or.inl lo)).trans (outside k (Or.inl lo))
  by_cases hi : mulBase g (c*N.internal) (c*N.cells) ≤ k
  · exact (rowStores_outside _ fit _ initial k (Or.inr hi)).trans (outside k (Or.inr hi))
  obtain ⟨a, rfl⟩ := exists_rowLocation (Nat.le_of_not_gt lo) (Nat.lt_of_not_ge hi)
  exact N.repeatedStores_read c connect code updates pin hidden fit initial a

include fintypeF semiringF

theorem repeatedStores_wire (fit : mulBase g (c*N.internal) (c*N.cells) ≤ 2^w)
    (initial : Memory w) (i : Fin (c*N.cells)) (k : Fin 3) :
    after initial (N.repeatedStores c connect code updates) (cellsBase g (c*N.internal) + 11*i.val + k.val) =
      Fin.ofNat _ (sourceAddress ((N.repeated c connect updates).source i k)) :=
  (N.repeatedStores_read c connect code updates (fun _ => false) (fun _ => false)
    fit initial (i, .inl k)).trans
    (read_wireAddress (N.repeated c connect updates) code _ _ i k)

theorem repeatedStores_factor (fit : mulBase g (c*N.internal) (c*N.cells) ≤ 2^w)
    (initial : Memory w) (i : Fin (c*N.cells)) (v : Fin 3 → Bool) :
    after initial (N.repeatedStores c connect code updates) (cellsBase g (c*N.internal) + 11*i.val + (3+key v)) =
      code.encode ((N.repeated c connect updates).table i v) :=
  (N.repeatedStores_read c connect code updates (fun _ => false) (fun _ => false)
    fit initial (i, .inr ⟨key v, key_lt v⟩)).trans
    (read_factor (N.repeated c connect updates) code _ _ i v)

end ThreeFlat.BitNetwork

end OAI
