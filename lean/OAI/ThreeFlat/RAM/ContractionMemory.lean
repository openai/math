import OAI.ThreeFlat.BitNetwork
import OAI.ThreeFlat.RAM.Weighted
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Dense memory for the trivalent network evaluator

Each cell occupies eleven consecutive words, three addresses followed by its
eight coefficients. The multiplication table of the fixed coefficient field
occupies the last block.
-/

namespace ThreeFlat.RAM.BitLayout

open Computability.VPVNP.BurstRAM

private def prependCells {α : Type*} {n : ℕ} (f : Fin n → α) (rest : ℕ → α) (i : ℕ) : α :=
  if h : i < n then f ⟨i, h⟩ else rest (i - n)

private theorem prefix_get {α : Type*} {n : ℕ} (f : Fin n → α) (rest : ℕ → α) (i : Fin n) :
    prependCells f rest i = f i := by simp [prependCells, i.isLt]

private theorem prefix_skip {α : Type*} {n : ℕ} (f : Fin n → α) (rest : ℕ → α) (i : ℕ) :
    prependCells f rest (n + i) = rest i := by simp [prependCells]

private theorem prefix_update {α : Type*} {n : ℕ} (f : Fin n → α) (rest : ℕ → α)
    (j : Fin n) (a : α) :
    prependCells (Function.update f j a) rest = Function.update (prependCells f rest) j.val a := by
  funext i
  by_cases he : i = j.val
  · subst i; simp [prefix_get]
  · rw [Function.update_of_ne he]
    by_cases h : i < n
    · simp [prependCells, h, Function.update_of_ne (show (⟨i,h⟩ : Fin n) ≠ j from
          fun hh => he (congrArg Fin.val hh))]
    · simp [prependCells, h]

private theorem prefix_update_tail {α : Type*} {n : ℕ} (f : Fin n → α) (rest : ℕ → α)
    (j : ℕ) (a : α) :
    prependCells f (Function.update rest j a) = Function.update (prependCells f rest) (n + j) a := by
  funext i
  by_cases hi : i < n
  · have hne : i ≠ n + j := by omega
    simp [prependCells, hi, Function.update_of_ne hne]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
    by_cases h : k = j
    · subst k; simp [prefix_skip]
    · have hnk : n + k ≠ n + j := by omega
      simp [prefix_skip, Function.update_of_ne h, Function.update_of_ne hnk]

private def rows {α : Type*} {n m : ℕ} (hm : 0 < m)
    (f : Fin n → Fin m → α) (rest : ℕ → α) : ℕ → α :=
  prependCells (n := n * m) (fun i => f ⟨i.val / m, (Nat.div_lt_iff_lt_mul hm).mpr i.isLt⟩
    ⟨i.val % m, Nat.mod_lt _ hm⟩) rest

private theorem rows_get {α : Type*} {n m : ℕ} (hm : 0 < m) (f : Fin n → Fin m → α)
    (rest : ℕ → α) (i : Fin n) (j : Fin m) :
    rows hm f rest (m * i + j) = f i j := by
  have h : m * i.val + j.val < n * m := by
    calc
      _ < m * i.val + m := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * m := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm i.val m]
      _ ≤ _ := Nat.mul_le_mul_right m i.isLt
  simp [rows, prependCells, h, Nat.mul_add_div hm, Nat.div_eq_of_lt j.isLt, Nat.mod_eq_of_lt j.isLt]

private theorem rows_skip {α : Type*} {n m : ℕ} (hm : 0 < m) (f : Fin n → Fin m → α)
    (rest : ℕ → α) (j : ℕ) : rows hm f rest (n * m + j) = rest j := prefix_skip _ _ _

def hiddenBase (p : ℕ) := 2 + p
def cellsBase (p hidden : ℕ) := hiddenBase p + hidden
def mulBase (p hidden cells : ℕ) := cellsBase p hidden + 11 * cells

def bitWord (w : ℕ) (b : Bool) : Word w := Fin.ofNat _ b.toNat

def sourceAddress {n p : ℕ} : BitSource n p → ℕ
  | .hidden i => hiddenBase p + i.val
  | .pin i => 2 + i.val
  | .constant b => b.toNat

def key (v : Fin 3 → Bool) : ℕ := (v 0).toNat + 2 * (v 1).toNat + 4 * (v 2).toNat
def bits (j : ℕ) : Fin 3 → Bool := fun i => j.testBit i.val

private theorem bits_key (v : Fin 3 → Bool) : bits (key v) = v := by
  revert v; decide

theorem key_lt (v : Fin 3 → Bool) : key v < 8 := by revert v; decide

variable {F : Type*} {p w : ℕ}

/-- The physical word at an offset inside the eleven-word cell record. -/
def record (N : BitNetwork F p) (code : FieldCode F w) (i : Fin N.cells)
    (j : Fin 11) : Word w :=
  if h : j.val < 3 then Fin.ofNat _ (sourceAddress (N.source i ⟨j.val,h⟩))
  else code.encode (N.table i (bits (j.val - 3)))

/-- One addressable finite array for the initial memory and every intermediate
assignment of the hidden bits. -/
noncomputable def memoryWithTail [Fintype F] [Semiring F] (tail : Memory w) (N : BitNetwork F p) (code : FieldCode F w)
    (pin : Fin p → Bool) (hidden : Fin N.internal → Bool) : Memory w :=
  prependCells (n := 2) (fun i => Fin.ofNat _ i.val) <|
  prependCells (fun i => bitWord w (pin i)) <|
  prependCells (fun i => bitWord w (hidden i)) <|
  rows (by decide : 0 < 11) (record N code) <|
  rows Fintype.card_pos
    (fun i j => code.encode ((Fintype.equivFin F).symm i * (Fintype.equivFin F).symm j))
    tail

/-- Zero-filled storage after the encoded field table. -/
noncomputable abbrev memory [Fintype F] [Semiring F] (N : BitNetwork F p) (code : FieldCode F w)
    (pin : Fin p → Bool) (hidden : Fin N.internal → Bool) : Memory w :=
  memoryWithTail (fun _ => 0) N code pin hidden

variable [Fintype F] [Semiring F]
variable (N : BitNetwork F p) (code : FieldCode F w) (pin : Fin p → Bool)
    (hidden : Fin N.internal → Bool)

theorem read_source (s : BitSource N.internal p) (tail : Memory w := fun _ => 0) :
    memoryWithTail tail N code pin hidden (sourceAddress s) = bitWord w (s.read hidden pin) := by
  cases s with
  | hidden i =>
    simp only [sourceAddress, BitSource.read, hiddenBase, Nat.add_assoc, memoryWithTail, prefix_skip,
      prefix_get]
  | pin i =>
    simp only [sourceAddress, BitSource.read, memoryWithTail, prefix_skip, prefix_get]
  | constant b =>
    cases b <;> simp [sourceAddress, BitSource.read, memoryWithTail, prependCells, bitWord]

theorem read_record (i : Fin N.cells) (j : Fin 11) (tail : Memory w := fun _ => 0) :
    memoryWithTail tail N code pin hidden (cellsBase p N.internal + 11*i.val+j.val) =
      record N code i j := by
  simp only [memoryWithTail, cellsBase, hiddenBase, Nat.add_assoc, prefix_skip]
  exact rows_get _ _ _ i j

theorem read_wireAddress (i : Fin N.cells) (j : Fin 3) (tail : Memory w := fun _ => 0) :
    memoryWithTail tail N code pin hidden (cellsBase p N.internal + 11 * i.val + j.val) =
      Fin.ofNat _ (sourceAddress (N.source i j)) := by
  simp only [memoryWithTail, cellsBase, hiddenBase, Nat.add_assoc, prefix_skip]
  rw [show j.val = ((⟨j.val, by omega⟩ : Fin 11) : ℕ) from rfl, rows_get]
  simp [record, j.isLt]

theorem read_factor (i : Fin N.cells) (v : Fin 3 → Bool) (tail : Memory w := fun _ => 0) :
    memoryWithTail tail N code pin hidden (cellsBase p N.internal + 11 * i.val + (3 + key v)) =
      code.encode (N.table i v) := by
  simp only [memoryWithTail, cellsBase, hiddenBase, Nat.add_assoc, prefix_skip]
  let j : Fin 11 := ⟨3 + key v, by have := key_lt v; omega⟩
  change rows _ _ _ (11 * i.val + j.val) = _
  rw [rows_get]
  simp [record, j, bits_key]

theorem read_product (a b : F) (tail : Memory w := fun _ => 0) :
    memoryWithTail tail N code pin hidden
        (mulBase p N.internal N.cells + Fintype.card F * ((Fintype.equivFin F) a).val +
          ((Fintype.equivFin F) b).val) = code.encode (a * b) := by
  simp only [memoryWithTail, mulBase, cellsBase, hiddenBase, Nat.add_assoc, prefix_skip]
  rw [Nat.mul_comm 11 N.cells, rows_skip, rows_get]
  simp

theorem write_hidden (i : Fin N.internal) (b : Bool) (hi : hiddenBase p + i.val < 2^w) (tail : Memory w := fun _ => 0) :
    writeMemory (memoryWithTail tail N code pin hidden) ⟨hiddenBase p + i.val, hi⟩ (bitWord w b) =
      memoryWithTail tail N code pin (Function.update hidden i b) := by
  have lift : (fun j => bitWord w (Function.update hidden i b j)) =
      Function.update (fun j => bitWord w (hidden j)) i (bitWord w b) := by
    funext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  rw [memoryWithTail, memoryWithTail, lift, prefix_update, prefix_update_tail, prefix_update_tail]
  funext a
  by_cases h : a = hiddenBase p + i.val
  · subst a; simp [writeMemory, hiddenBase, Nat.add_assoc]
  · have h' : a ≠ 2 + (p + i.val) := by simpa [hiddenBase, Nat.add_assoc] using h
    simp [writeMemory, h, h', Function.update_of_ne]

/-- First address outside the input, workspace, cells and multiplication table. -/
def footprint (N : BitNetwork F p) : ℕ :=
  mulBase p N.internal N.cells + Fintype.card F * Fintype.card F

private theorem prepend_agrees {α : Type*} {n k : ℕ} (f : Fin n → α) {x y : ℕ → α}
    (h : ∀ a < k, x a = y a) (i : ℕ) (hi : i < n+k) :
    prependCells f x i = prependCells f y i := by
  unfold prependCells
  split_ifs with hn
  · rfl
  · exact h _ (by omega)

theorem memoryWithTail_agrees (tail : Memory w) (i : ℕ) (hi : i < footprint N) :
    memoryWithTail tail N code pin hidden i = memory N code pin hidden i := by
  unfold memory memoryWithTail rows
  refine prepend_agrees _ (k := p + (N.internal + (N.cells * 11 + (Fintype.card F * Fintype.card F + 0)))) ?_ i ?_
  · refine prepend_agrees _ (k := N.internal + (N.cells*11 + (Fintype.card F * Fintype.card F + 0))) ?_
    refine prepend_agrees _ (k := N.cells*11 + (Fintype.card F * Fintype.card F + 0)) ?_
    refine prepend_agrees _ (k := Fintype.card F * Fintype.card F + 0) ?_
    refine prepend_agrees _ (k := 0) ?_
    intro j hj
    omega
  · simp only [footprint, mulBase, cellsBase, hiddenBase] at hi
    rw [Nat.mul_comm N.cells 11]
    omega

theorem memoryWithTail_after (tail : Memory w) (j : ℕ) :
    memoryWithTail tail N code pin hidden (footprint N + j) = tail j := by
  have addr : footprint N + j =
      2 + (p + (N.internal + (N.cells*11 + (Fintype.card F * Fintype.card F + j)))) := by
    simp only [footprint, mulBase, cellsBase, hiddenBase, Nat.mul_comm N.cells 11]
    omega
  simp only [addr, memoryWithTail, rows, prefix_skip]

/-- Any memory with the prescribed prefix has a unique suffix address space. -/
theorem memoryWithTail_eq_of_prefix (m : Memory w)
    (h : ∀ i < footprint N, m i = memory N code pin hidden i) :
    memoryWithTail (fun j => m (footprint N+j)) N code pin hidden = m := by
  funext i
  by_cases hi : i < footprint N
  · exact (memoryWithTail_agrees N code pin hidden _ i hi).trans (h i hi).symm
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
    exact memoryWithTail_after N code pin hidden _ j

end ThreeFlat.RAM.BitLayout

end OAI
