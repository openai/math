import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Synchronized monomial and shear layers

Each step of a word reserves one monomial slot followed by one shear slot.
The unused slot is the identity. Disjoint parallel calls and tensor products
can therefore share a common depth, independently of the number of calls.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix
open scoped BigOperators Kronecker

/-- The finite tensor product, indexed by tuples of coordinates. -/
def gridTensor {K : Type*} [CommMonoid K] {ι : Type*} [Fintype ι] {I : ι → Type*}
    (A : ∀ i, Matrix (I i) (I i) K) : Matrix (∀ i, I i) (∀ i, I i) K :=
  fun x y => ∏ i, A i (x i) (y i)

theorem gridTensor_one {K ι : Type*} [CommSemiring K] [Fintype ι] {I : ι → Type*}
    [∀ i, DecidableEq (I i)] [DecidableEq (∀ i, I i)] :
    gridTensor (fun i => (1 : Matrix (I i) (I i) K)) = 1 := by
  classical
  ext x y
  by_cases h : x = y
  · subst y
    simp [gridTensor]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      contrapose! h
      exact funext h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

theorem gridTensor_mul {K ι : Type*} [CommSemiring K] [Fintype ι] {I : ι → Type*}
    [∀ i, Fintype (I i)] [DecidableEq ι] (A B : ∀ i, Matrix (I i) (I i) K) :
    gridTensor (fun i => A i * B i) = gridTensor A * gridTensor B := by
  ext x y
  simp only [gridTensor, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

/-- The two types of layers in the grid construction. -/
inductive LayerKind where
  | monomial | shear

/-- The elementary shear, with its first register incremented by its second. -/
def unitShear (K : Type*) [Zero K] [One K] : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]

/-- Monomial layers are permutations and unit scalings. Shear layers are
disjoint blocks of tensor powers of the elementary shear, allowing a
permutation of the register labels. Both descriptions are stable under
tensor products and disjoint parallel composition. -/
inductive LayerMatrix {K : Type*} [CommSemiring K] :
    (kind : LayerKind) → {I : Type} → [Fintype I] → [DecidableEq I] → Matrix I I K → Prop where
  | id (kind) {I : Type} [Fintype I] [DecidableEq I] :
      LayerMatrix kind (1 : Matrix I I K)
  | monomial {I : Type} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) (d : I → Kˣ) :
      LayerMatrix .monomial (fun i j => if e i = j then (d i : K) else 0)
  | unitShear : LayerMatrix .shear (FiniteFourier.unitShear K)
  | relabel {kind I J} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      {A : Matrix I I K} (e : I ≃ J) (hA : LayerMatrix kind A) :
      LayerMatrix kind (A.submatrix e.symm e.symm)
  | tensor {kind I J} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      {A : Matrix I I K} {B : Matrix J J K} (hA : LayerMatrix kind A) (hB : LayerMatrix kind B) :
      LayerMatrix kind (A ⊗ₖ B)
  | parallel {kind I J} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      {A : Matrix I I K} {B : Matrix J J K} (hA : LayerMatrix kind A) (hB : LayerMatrix kind B) :
      LayerMatrix kind (Matrix.fromBlocks A 0 0 B)
  | grid {kind ι} [Fintype ι] [DecidableEq ι] {I : ι → Type}
      [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
      {A : ∀ i, Matrix (I i) (I i) K} (hA : ∀ i, LayerMatrix kind (A i)) :
      LayerMatrix kind (gridTensor A)
  | blocks {kind ι} [Fintype ι] [DecidableEq ι] {I : ι → Type}
      [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
      {A : ∀ i, Matrix (I i) (I i) K} (hA : ∀ i, LayerMatrix kind (A i)) :
      LayerMatrix kind (Matrix.blockDiagonal' A)

variable {K : Type*} [CommSemiring K] {I J : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- A diagonal with unit entries is a monomial layer over a ring. -/
theorem layerMatrix_diagonal_units {d : I → K} (hd : ∀ i, IsUnit (d i)) :
    LayerMatrix .monomial (diagonal d) := by
  have h : diagonal d = (fun i j => if (Equiv.refl I) i = j then ((hd i).unit : K) else 0) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h]
  exact LayerMatrix.monomial (Equiv.refl I) fun i => (hd i).unit

/-- A diagonal with nonzero entries is a monomial layer over a field. -/
theorem layerMatrix_diagonal {F : Type*} [Field F] {d : I → F} (hd : ∀ i, d i ≠ 0) :
    LayerMatrix .monomial (diagonal d) :=
  layerMatrix_diagonal_units fun i => isUnit_iff_ne_zero.mpr (hd i)

/-- A word with exactly `d` monomial/shear pairs, including any padding. -/
def LayerWord : ℕ → Matrix I I K → Prop
  | 0, A => A = 1
  | d + 1, A => ∃ M S P, LayerMatrix .monomial M ∧ LayerMatrix .shear S ∧
      LayerWord d P ∧ A = S * M * P

theorem layerWord_one (d : ℕ) : LayerWord d (1 : Matrix I I K) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ⟨1, 1, 1, .id _, .id _, ih, by simp⟩

theorem layerWord_of_layer {k : LayerKind} {A : Matrix I I K} (h : LayerMatrix k A) :
    LayerWord 1 A := by
  cases k with
  | monomial => exact ⟨A, 1, 1, h, .id _, rfl, by simp⟩
  | shear => exact ⟨1, A, 1, .id _, h, rfl, by simp⟩

theorem layerWord_mul {d e : ℕ} {A B : Matrix I I K} (hA : LayerWord d A)
    (hB : LayerWord e B) : LayerWord (d + e) (A * B) := by
  induction d generalizing A with
  | zero =>
    obtain rfl : A = 1 := hA
    simpa using hB
  | succ d ih =>
    obtain ⟨M, S, P, hM, hS, hP, rfl⟩ := hA
    rw [Nat.succ_add]
    exact ⟨M, S, P * B, hM, hS, ih hP, Matrix.mul_assoc _ _ _⟩

theorem LayerWord.pad {d e : ℕ} (hde : d ≤ e) {A : Matrix I I K} (hA : LayerWord d A) :
    LayerWord e A := by
  simpa [Nat.add_sub_of_le hde] using layerWord_mul hA (layerWord_one (I := I) (K := K) (e - d))

theorem layerWord_tensor {d : ℕ} {A : Matrix I I K} {B : Matrix J J K}
    (hA : LayerWord d A) (hB : LayerWord d B) : LayerWord d (A ⊗ₖ B) := by
  induction d generalizing A B with
  | zero => exact (congrArg₂ Matrix.kronecker hA hB).trans Matrix.one_kronecker_one
  | succ d ih =>
    obtain ⟨M, S, P, hM, hS, hP, rfl⟩ := hA
    obtain ⟨N, T, Q, hN, hT, hQ, rfl⟩ := hB
    exact ⟨M ⊗ₖ N, S ⊗ₖ T, P ⊗ₖ Q, .tensor hM hN, .tensor hS hT, ih hP hQ, by
      rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]⟩

theorem layerWord_parallel {d : ℕ} {A : Matrix I I K} {B : Matrix J J K}
    (hA : LayerWord d A) (hB : LayerWord d B) : LayerWord d (Matrix.fromBlocks A 0 0 B) := by
  induction d generalizing A B with
  | zero =>
    obtain rfl : A = 1 := hA
    obtain rfl : B = 1 := hB
    exact Matrix.fromBlocks_one
  | succ d ih =>
    obtain ⟨M, S, P, hM, hS, hP, rfl⟩ := hA
    obtain ⟨N, T, Q, hN, hT, hQ, rfl⟩ := hB
    exact ⟨_, _, _, .parallel hM hN, .parallel hS hT, ih hP hQ, by simp [Matrix.fromBlocks_multiply]⟩

theorem LayerWord.relabel {d : ℕ} {A : Matrix I I K} (hA : LayerWord d A) (e : I ≃ J) :
    LayerWord d (A.submatrix e.symm e.symm) := by
  induction d generalizing A with
  | zero =>
    obtain rfl : A = 1 := hA
    exact Matrix.submatrix_one_equiv e.symm
  | succ d ih =>
    obtain ⟨M, S, P, hM, hS, hP, rfl⟩ := hA
    exact ⟨_, _, _, .relabel e hM, .relabel e hS, ih hP, by
      simp only [Matrix.submatrix_mul_equiv]⟩

section Family

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Type}
  [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- Tensoring any number of words uses the same number of slot pairs. -/
theorem layerWord_grid {d : ℕ} {A : ∀ i, Matrix (P i) (P i) K} (h : ∀ i, LayerWord d (A i)) :
    LayerWord d (gridTensor A) := by
  induction d generalizing A with
  | zero =>
    exact (congrArg gridTensor (funext fun i => (h i : A i = 1))).trans gridTensor_one
  | succ d ih =>
    choose M S R hM hS hR ha using h
    rw [show A = fun i => S i * M i * R i from funext ha]
    exact ⟨_, _, _, .grid hM, .grid hS, ih hR, by rw [gridTensor_mul, gridTensor_mul]⟩

/-- Disjoint calls on independently sized blocks can run in parallel at the same depth. -/
theorem layerWord_blocks {d : ℕ} {A : ∀ i, Matrix (P i) (P i) K} (h : ∀ i, LayerWord d (A i)) :
    LayerWord d (Matrix.blockDiagonal' A) := by
  induction d generalizing A with
  | zero =>
    exact (congrArg Matrix.blockDiagonal' (funext fun i => (h i : A i = 1))).trans
      Matrix.blockDiagonal'_one
  | succ d ih =>
    choose M S R hM hS hR ha using h
    rw [show A = fun i => S i * M i * R i from funext ha]
    exact ⟨_, _, _, .blocks hM, .blocks hS, ih hR, by
      rw [Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_mul]⟩

end Family

/-- A word using occupied workspace can be run with a larger workspace.
The auxiliary registers retain their arbitrary initial contents. -/
theorem LayerWord.enlargeWorkspace {W V : Type} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V] {d : ℕ} {A : Matrix I I K}
    (h : LayerWord d (Matrix.fromBlocks A 0 0 (1 : Matrix W W K)))
    (hle : Fintype.card W ≤ Fintype.card V) :
    LayerWord d (Matrix.fromBlocks A 0 0 (1 : Matrix V V K)) := by
  let R := Fin (Fintype.card V - Fintype.card W)
  let e : W ⊕ R ≃ V := Fintype.equivOfCardEq (by simpa [R] using Nat.add_sub_of_le hle)
  let Q := Matrix.fromBlocks (Matrix.fromBlocks A 0 0 (1 : Matrix W W K)) 0 0 (1 : Matrix R R K)
  have hQ : LayerWord d Q := layerWord_parallel h (layerWord_one _)
  have hS := hQ.relabel (Equiv.sumAssoc I W R)
  have heq : Q.submatrix (Equiv.sumAssoc I W R).symm (Equiv.sumAssoc I W R).symm =
      Matrix.fromBlocks A 0 0 (1 : Matrix (W ⊕ R) (W ⊕ R) K) := by
    ext i j
    rcases i with i | (w | r) <;> rcases j with j | (v | t) <;>
      simp [Q, Matrix.submatrix, Matrix.fromBlocks, Matrix.one_apply]
  rw [heq] at hS
  have hT := hS.relabel ((Equiv.refl I).sumCongr e)
  convert hT using 1
  ext i j
  rcases i with i | w <;> rcases j with j | v <;>
    simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.one_apply]

/-- Separate one designated fiber from all other registers. -/
private def splitFiber (I : Type) {J : Type} [DecidableEq J] (j : J) :
    I × J ≃ I ⊕ (I × {k : J // k ≠ j}) where
  toFun p := if h : p.2 = j then Sum.inl p.1 else Sum.inr (p.1, ⟨p.2, h⟩)
  invFun := Sum.elim (fun i => (i, j)) (fun p => (p.1, p.2.val))
  left_inv := by rintro ⟨x, k⟩; by_cases hk : k = j <;> simp [hk]
  right_inv := by rintro (x | ⟨x, k, hk⟩) <;> simp_all

/-- Apply an axis matrix to one fiber while borrowing and restoring registers
from the other fibers. No external coordinates are needed. -/
theorem LayerWord.applyOccupiedFiber {W : Type} [Fintype W] [DecidableEq W]
    {d : ℕ} {A : Matrix I I K} (h : LayerWord d (Matrix.fromBlocks A 0 0 (1 : Matrix W W K)))
    (j : J) (hc : Fintype.card W ≤ Fintype.card I * (Fintype.card J - 1)) :
    LayerWord d (Matrix.blockDiagonal (fun k : J => if k = j then A else 1)) := by
  have hcap : Fintype.card W ≤ Fintype.card (I × {k : J // k ≠ j}) := by
    simpa [Fintype.card_subtype_compl] using hc
  have hQ := (h.enlargeWorkspace hcap).relabel (splitFiber I j).symm
  convert hQ using 1
  ext ⟨x, k⟩ ⟨y, l⟩
  by_cases hk : k = j <;> by_cases hl : l = j <;> by_cases hkl : k = l <;>
    simp_all [Matrix.blockDiagonal_apply, Matrix.submatrix, splitFiber,
      Matrix.fromBlocks, Matrix.one_apply, Prod.ext_iff]

/-- Process a finite group of fibers in turn, using the same occupied registers
at each call. After all the calls the whole group has the axis matrix on every fiber. -/
theorem LayerWord.traverseOccupiedFibers {W : Type} [Fintype W] [DecidableEq W]
    {d : ℕ} {A : Matrix I I K} (h : LayerWord d (Matrix.fromBlocks A 0 0 (1 : Matrix W W K)))
    (hc : Fintype.card W ≤ Fintype.card I * (Fintype.card J - 1)) :
    LayerWord (Fintype.card J * d) (Matrix.blockDiagonal (fun _ : J => A)) := by
  have hS (s : Finset J) :
      LayerWord (s.card * d) (Matrix.blockDiagonal fun k : J => if k ∈ s then A else 1) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.card_empty, Nat.zero_mul, Finset.notMem_empty, ite_false]
      exact Matrix.blockDiagonal_one
    | insert j s hj ih =>
      have hprod := layerWord_mul (h.applyOccupiedFiber j hc) ih
      rw [← Matrix.blockDiagonal_mul] at hprod
      rw [Finset.card_insert_of_notMem hj, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      convert hprod using 2
      funext k
      by_cases hk : k = j
      · subst k
        simp [hj]
      · simp [hk]
  simpa using hS Finset.univ

/-- Partition a finite index set into groups whose sizes lie between `c` and
`2*c-1`. The remainder is added to the first group. -/
theorem exists_fiber_partition (J : Type) [Fintype J] {c : ℕ} (hc : 0 < c)
    (hcJ : c ≤ Fintype.card J) :
    ∃ (b : ℕ) (size : Fin b → ℕ), (∀ j, c ≤ size j ∧ size j < 2 * c) ∧
      Nonempty (J ≃ Σ j, Fin (size j)) := by
  let n := Fintype.card J
  let b := n / c
  have hb : 0 < b := Nat.div_pos hcJ hc
  let first : Fin b := ⟨0, hb⟩
  let size (j : Fin b) := c + if j = first then n % c else 0
  refine ⟨b, size, ?_, ⟨Fintype.equivOfCardEq ?_⟩⟩
  · intro j
    have hrem := Nat.mod_lt n hc
    dsimp [size]
    split <;> omega
  · rw [Fintype.card_sigma]
    simp [size, Finset.sum_add_distrib, b, Nat.mul_comm _ c, Nat.div_add_mod, n]

/-- Regroup the columns of a rectangular array according to an arbitrary
partition of the fiber indices. -/
private def regroupFibers {B : Type} (F : B → Type) (I : Type) :
    I × (Σ j, F j) ≃ (Σ j, I × F j) where
  toFun x := ⟨x.2.1, (x.1, x.2.2)⟩
  invFun x := (x.2.1, ⟨x.1, x.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The axis step in the occupied-fibers lemma. Partition a large family into
groups, borrow from the other fibers of each group, and run the groups in
parallel. The bound depends on the capacity ratio and the input word depth,
independently of the total number of fibers. -/
theorem LayerWord.synchronizeOccupiedFibers {W : Type} [Fintype W] [DecidableEq W]
    {d c : ℕ} {A : Matrix I I K} (h : LayerWord d (Matrix.fromBlocks A 0 0 (1 : Matrix W W K)))
    (hc : 0 < c) (hcJ : c ≤ Fintype.card J)
    (hcW : Fintype.card W ≤ Fintype.card I * (c - 1)) :
    LayerWord ((2 * c - 1) * d) (Matrix.blockDiagonal (fun _ : J => A)) := by
  obtain ⟨b, size, hs, ⟨e⟩⟩ := exists_fiber_partition J hc hcJ
  have hF (j : Fin b) : LayerWord ((2 * c - 1) * d)
      (Matrix.blockDiagonal fun _ : Fin (size j) => A) := by
    apply LayerWord.pad (hA := h.traverseOccupiedFibers (J := Fin (size j)) ?_)
    · simp
      exact Nat.mul_le_mul_right d (by have := hs j; omega)
    · rw [Fintype.card_fin]
      exact hcW.trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hs j).1 1))
  have hG := (layerWord_blocks hF).relabel (regroupFibers (fun j => Fin (size j)) I).symm
  have hM : (Matrix.blockDiagonal' (fun j => Matrix.blockDiagonal fun _ : Fin (size j) => A)).submatrix
      (regroupFibers (fun j => Fin (size j)) I) (regroupFibers (fun j => Fin (size j)) I) =
      Matrix.blockDiagonal (fun _ : Σ j, Fin (size j) => A) := by
    ext ⟨x, j, u⟩ ⟨y, k, v⟩
    by_cases h : j = k
    · subst k
      simp [Matrix.submatrix, regroupFibers, Matrix.blockDiagonal_apply]
    · simp [Matrix.submatrix, regroupFibers, Matrix.blockDiagonal'_apply', Matrix.blockDiagonal_apply,
        h, Sigma.ext_iff]
  simp only [Equiv.symm_symm] at hG
  rw [hM] at hG
  have hT := hG.relabel ((Equiv.refl I).prodCongr e.symm)
  convert hT using 1
  ext ⟨x, j⟩ ⟨y, k⟩
  simp [Matrix.submatrix, Matrix.blockDiagonal_apply]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
