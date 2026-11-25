import OAI.Computability.NearSquareRoot.KernelCyclotomicCode

/-! # Restriction of binary pencil coefficients to dyadic rows

Multiplication by a fixed element of the repair algebra uses its signed
circulant coefficient matrix. Replacing each entry of a matrix by this block
acts on all basis components of every input and output row. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilDescent

open CyclotomicCode
open scoped CyclotomicCode Matrix

variable {a : ℕ} {I J K : Type*}

abbrev Coord (a : ℕ) := Fin (2 ^ a)

/-- Coefficient of input component `j` in output component `k` after
multiplication by `r` modulo `X^(2^a) + 1`. -/
def scalarBlock (r : Number a) (k j : Coord a) : Dyadic :=
  if (k-j).val + j.val < 2 ^ a then r.coeffs (k-j) else -r.coeffs (k-j)

theorem scalarBlock_mulVec (r x : Number a) (k : Coord a) :
    ((scalarBlock r : Matrix _ _ _) *ᵥ x.coeffs) k = (r * x).coeffs k := by
  change ∑ j, scalarBlock r k j * x.coeffs j = times a r.coeffs x.coeffs k
  unfold times
  rw [Finset.sum_comm (f := fun i j : Coord a =>
    if (i.val + j.val) % 2 ^ a = k.val then
      (if i.val + j.val < 2 ^ a then r.coeffs i * x.coeffs j else -(r.coeffs i * x.coeffs j))
    else 0)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (k - j)]
  · have h : ((k-j).val + j.val) % (2^a) = k.val :=
      congrArg Fin.val (sub_add_cancel k j)
    simp only [h, ↓reduceIte, scalarBlock]
    split <;> simp
  · intro i _ hi
    have h : (i.val + j.val) % (2^a) ≠ k.val := by
      intro he
      exact hi (eq_sub_iff_add_eq.mpr (Fin.ext he))
    simp [h]
  · simp

/-- Entrywise expansion of an extension matrix to a dyadic matrix. -/
def flatten (M : Matrix I J (Number a)) : Matrix (I × Coord a) (J × Coord a) Dyadic :=
  fun k j => scalarBlock (M k.1 j.1) k.2 j.2

def unpack (x : I → Number a) (p : I × Coord a) : Dyadic := (x p.1).coeffs p.2

def pack (x : I × Coord a → Dyadic) (i : I) : Number a := ⟨fun j => x (i,j)⟩

@[simp] theorem pack_unpack (x : I → Number a) : pack (unpack x) = x := rfl
@[simp] theorem unpack_pack (x : I × Coord a → Dyadic) : unpack (pack x) = x := rfl

private def coeffAdd (k : Coord a) : Number a →+ Dyadic where
  toFun x := x.coeffs k
  map_zero' := rfl
  map_add' _ _ := rfl

/-- One multiplication of extension rows is one simultaneous multiplication
on the expanded dyadic rows, for every assignment to the dyadic inputs. -/
theorem flatten_mulVec [Fintype J] (M : Matrix I J (Number a)) (x : J × Coord a → Dyadic) :
    flatten M *ᵥ x = unpack (M *ᵥ pack x) := by
  funext ⟨i, k⟩
  change (∑ j : J × Coord a, scalarBlock (M i j.1) k j.2 * x j) =
    coeffAdd k (∑ j : J, M i j * pack x j)
  rw [Fintype.sum_prod_type, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact scalarBlock_mulVec (M i j) (pack x j) k

/-- Composition of extension-valued stages is preserved by flattening. -/
theorem flatten_mul [Fintype J] [Fintype K]
    (M : Matrix I J (Number a)) (N : Matrix J K (Number a)) :
    flatten (M * N) = flatten M * flatten N := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [flatten_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flatten_mulVec, flatten_mulVec,
    pack_unpack]

theorem flatten_zero : flatten (0 : Matrix I J (Number a)) = 0 := by
  ext ⟨i,k⟩ ⟨j,t⟩
  change (if _ then (0 : Dyadic) else -0) = 0
  simp

theorem flatten_add (M N : Matrix I J (Number a)) :
    flatten (M + N) = flatten M + flatten N := by
  ext ⟨i,k⟩ ⟨j,t⟩
  change scalarBlock (M i j + N i j) k t =
    scalarBlock (M i j) k t + scalarBlock (N i j) k t
  unfold scalarBlock
  by_cases h : (k - t).val + t.val < 2^a
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    exact neg_add _ _

theorem flatten_one [Fintype I] [DecidableEq I] :
    flatten (1 : Matrix I I (Number a)) = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [flatten_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, unpack_pack]

theorem flatten_pow [Fintype I] [DecidableEq I] (M : Matrix I I (Number a)) (b : ℕ) :
    flatten (M ^ b) = flatten M ^ b := by
  induction b with
  | zero => simp [flatten_one]
  | succ b ih => rw [pow_succ, pow_succ, flatten_mul, ih]

/-- A dyadic entry acts diagonally on the coefficient components. -/
theorem scalarBlock_ofBase (r : Dyadic) (k j : Coord a) :
    scalarBlock (Number.ofBase a r) k j = if k = j then r else 0 := by
  by_cases hk : k = j
  · subst k
    simp [scalarBlock, Number.ofBase, j.isLt]
  · have hsub : k - j ≠ 0 := sub_ne_zero.mpr hk
    have hval : (k-j).val ≠ 0 := fun h => hsub (Fin.ext h)
    dsimp only [scalarBlock, Number.ofBase]
    simp [hk, hval]

/-- A dyadic recursive axis call acts independently on each basis component. -/
theorem flatten_base_apply (M : Matrix I J Dyadic) (i : I) (j : J) (k t : Coord a) :
    flatten (M.map (Number.ofBase a)) (i,k) (j,t) = if k = t then M i j else 0 :=
  scalarBlock_ofBase (M i j) k t

theorem flatten_base_mulVec [Fintype J] (M : Matrix I J Dyadic) (x : J × Coord a → Dyadic)
    (i : I) (k : Coord a) :
    (flatten (M.map (Number.ofBase a)) *ᵥ x) (i,k) = (M *ᵥ (fun j => x (j,k))) i := by
  change (∑ p : J × Coord a, flatten (M.map (Number.ofBase a)) (i,k) p * x p) = _
  rw [Fintype.sum_prod_type]
  simp [flatten_base_apply, ite_mul, Matrix.mulVec, dotProduct]

def flattenAddHom : Matrix I J (Number a) →+ Matrix (I × Coord a) (J × Coord a) Dyadic where
  toFun := flatten
  map_zero' := flatten_zero
  map_add' := flatten_add

theorem flatten_sub (M N : Matrix I J (Number a)) :
    flatten (M - N) = flatten M - flatten N := map_sub flattenAddHom M N

/-- Interpret an executable dyadic as a rational scalar. -/
def toRatHom : Dyadic →+* ℚ where
  toFun := Dyadic.toRat
  map_zero' := rfl
  map_one' := rfl
  map_mul' := Dyadic.toRat_mul
  map_add' := Dyadic.toRat_add

/-- Rational matrix for use in the exact semantics of the stream pass. -/
def flattenRat (M : Matrix I J (Number a)) : Matrix (I × Coord a) (J × Coord a) ℚ :=
  (flatten M).map toRatHom

theorem flattenRat_zero : flattenRat (0 : Matrix I J (Number a)) = 0 := by
  rw [flattenRat, flatten_zero, Matrix.map_zero _ (map_zero _)]

theorem flattenRat_one [Fintype I] [DecidableEq I] :
    flattenRat (1 : Matrix I I (Number a)) = 1 := by
  rw [flattenRat, flatten_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem flattenRat_add (M N : Matrix I J (Number a)) :
    flattenRat (M + N) = flattenRat M + flattenRat N := by
  simp only [flattenRat, flatten_add, Matrix.map_add _ (map_add _)]

theorem flattenRat_sub (M N : Matrix I J (Number a)) :
    flattenRat (M - N) = flattenRat M - flattenRat N := by
  simp only [flattenRat, flatten_sub, Matrix.map_sub _ (map_sub _)]

theorem flattenRat_mul [Fintype J] [Fintype K] (M : Matrix I J (Number a)) (N : Matrix J K (Number a)) :
    flattenRat (M * N) = flattenRat M * flattenRat N := by
  simp only [flattenRat, flatten_mul, Matrix.map_mul]

theorem flattenRat_pow [Fintype I] [DecidableEq I] (M : Matrix I I (Number a)) (b : ℕ) :
    flattenRat (M ^ b) = flattenRat M ^ b := by
  induction b with
  | zero => simp [flattenRat_one]
  | succ b ih => rw [pow_succ, pow_succ, flattenRat_mul, ih]

end PencilDescent

end NearSquareRoot
end Computability
end OAI
