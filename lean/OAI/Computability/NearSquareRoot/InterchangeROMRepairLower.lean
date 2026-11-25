import OAI.Computability.NearSquareRoot.InterchangePackedPencil

/-! # Ground-field matrix coordinates for the binary repair pencil -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace InterchangeROMRepair.Lower

open OAI.LinearAlgebra.FiniteFourier Matrix SwapRepair
open NearSquareRoot.Interchange.PackedPencil (ClockPos rowIndex)

variable {K I J : Type} [Field K] {m : ℕ}

/-- Expand a vector of extension rows using the fixed power basis. -/
def flatten (x : I → Coeff K m) : I × BasisIndex m → K :=
  fun q => components K m (x q.1) q.2

def unflatten (x : I × BasisIndex m → K) : I → Coeff K m :=
  fun i => (components K m).symm (fun d => x (i,d))

@[simp] theorem flatten_unflatten (x : I × BasisIndex m → K) : flatten (unflatten x) = x := by
  funext ⟨i,d⟩
  simp [flatten,unflatten]

@[simp] theorem unflatten_flatten (x : I → Coeff K m) : unflatten (flatten x) = x := by
  funext i
  simp [flatten,unflatten]

def flatEquiv (K I : Type) [Field K] (m : ℕ) :
    (I → Coeff K m) ≃ₗ[K] (I × BasisIndex m → K) where
  toFun := flatten
  invFun := unflatten
  left_inv := unflatten_flatten
  right_inv := flatten_unflatten
  map_add' x y := by ext ⟨i,d⟩; simp [flatten]
  map_smul' c x := by ext ⟨i,d⟩; simp [flatten]

def flatMap [Fintype I] [DecidableEq I] (f : (I → Coeff K m) →ₗ[Coeff K m] (J → Coeff K m)) :
    Matrix (J × BasisIndex m) (I × BasisIndex m) K :=
  LinearMap.toMatrix' ((flatEquiv K J m).toLinearMap ∘ₗ
    ((f.restrictScalars K) ∘ₗ (flatEquiv K I m).symm.toLinearMap))

@[simp] theorem flatMap_mulVec [Fintype I] [DecidableEq I]
    (f : (I → Coeff K m) →ₗ[Coeff K m] (J → Coeff K m)) (x : I → Coeff K m) :
    flatMap f *ᵥ flatten x = flatten (f x) := by
  rw [flatMap,LinearMap.toMatrix'_mulVec]
  change flatten (f (unflatten (flatten x))) = _
  rw [unflatten_flatten]

/-- The check and synthesis operators have independent base-field matrices. -/
def flattenMatrix [Fintype I] [DecidableEq I] (A : Matrix J I (Coeff K m)) :
    Matrix (J × BasisIndex m) (I × BasisIndex m) K := flatMap A.mulVecLin

@[simp] theorem flattenMatrix_mulVec [Fintype I] [DecidableEq I] (A : Matrix J I (Coeff K m))
    (x : I → Coeff K m) : flattenMatrix A *ᵥ flatten x = flatten (A *ᵥ x) :=
  flatMap_mulVec A.mulVecLin _

/-- The four blocks of the sign-pattern table, with false denoting the first input or output. -/
def tableBlock (T : Table K m) (η : Pattern m) (out input : Bool) :
    (Fin (checks m) → Coeff K m) →ₗ[Coeff K m] (Fin (checks m) → Coeff K m) :=
  let E := Coeff K m
  let V := Fin (checks m) → E
  let embed := if input then LinearMap.inr E V V else LinearMap.inl E V V
  let project := if out then LinearMap.snd E V V else LinearMap.fst E V V
  project ∘ₗ ((T η) ∘ₗ embed)

def tableMatrix (T : Table K m) (η : Pattern m) (out input : Bool) :=
  flatMap (tableBlock T η out input)

theorem tableMatrix_mulVec (T : Table K m) (η : Pattern m) (out : Bool)
    (x y : Fin (checks m) → Coeff K m) :
    tableMatrix T η out false *ᵥ flatten x + tableMatrix T η out true *ᵥ flatten y =
      flatten (if out then (T η (x,y)).2 else (T η (x,y)).1) := by
  have h : T η (x,y) = T η (x,0) + T η (0,y) := by
    rw [← map_add]; simp
  rw [h]
  cases out <;> simp only [tableMatrix,flatMap_mulVec,tableBlock,Bool.false_eq_true,
    ite_false,ite_true,LinearMap.comp_apply,LinearMap.inl_apply,LinearMap.inr_apply,
    LinearMap.fst_apply,LinearMap.snd_apply,Prod.fst_add,Prod.snd_add] <;>
    exact ((flatEquiv K (Fin (checks m)) m).map_add _ _).symm

def rowEquiv (m : ℕ) : (Pattern m × ClockPos m) ≃ Fin (width m) := rowIndex m

/-- A matrix with one row block for each shift; inactive inter-block entries vanish. -/
def blockMatrix (A : Pattern m → Matrix (ClockPos m) (ClockPos m) (Coeff K m)) :
    Matrix (Fin (width m)) (Fin (width m)) (Coeff K m) :=
  fun i j =>
    let u := (rowEquiv m).symm i
    let v := (rowEquiv m).symm j
    if u.1 = v.1 then A u.1 u.2 v.2 else 0

theorem blockMatrix_mulVec (A : Pattern m → Matrix (ClockPos m) (ClockPos m) (Coeff K m))
    (β : Pattern m) (u : ClockPos m) (x : Fin (width m) → Coeff K m) :
    (blockMatrix A *ᵥ x) (rowEquiv m (β,u)) =
      (A β *ᵥ fun v => x (rowEquiv m (β,v))) u := by
  classical
  change (∑ j : Fin (width m), blockMatrix A (rowEquiv m (β,u)) j * x j) =
    ∑ v : ClockPos m, A β u v * x (rowEquiv m (β,v))
  rw [← Equiv.sum_comp (rowEquiv m) (fun j : Fin (width m) => blockMatrix A (rowEquiv m (β,u)) j * x j)]
  simp [blockMatrix, Fintype.sum_prod_type, ite_mul]

def mixerMatrix (A : Pattern m → Matrix (ClockPos m) (ClockPos m) (Coeff K m)) :=
  flattenMatrix (blockMatrix A)

/-- This dense matrix realizes precisely the pointwise row mixer of the staged bank. -/
theorem mixerMatrix_mulVec (A : Pattern m → Matrix (ClockPos m) (ClockPos m) (Coeff K m))
    (y : Fin (width m) × BasisIndex m → K) :
    mixerMatrix A *ᵥ y = Interchange.PackedPencil.mixer A y := by
  obtain ⟨x,rfl⟩ := (flatEquiv K (Fin (width m)) m).surjective y
  change mixerMatrix A *ᵥ flatten x = Interchange.PackedPencil.mixer A (flatten x)
  rw [mixerMatrix,flattenMatrix_mulVec]
  funext ⟨i,d⟩
  obtain ⟨⟨β,u⟩,rfl⟩ := (rowEquiv m).surjective i
  change components K m ((blockMatrix A *ᵥ x) (rowEquiv m (β,u))) d =
    Interchange.PackedPencil.mixer A (flatten x) (rowEquiv m (β,u),d)
  rw [blockMatrix_mulVec]
  change components K m (∑ v, A β u v * x (rowEquiv m (β,v))) d = _
  rw [map_sum,Finset.sum_apply]
  have hr : (rowIndex m).symm (rowEquiv m (β,u)) = (β,u) := (rowEquiv m).symm_apply_apply _
  simp only [Interchange.PackedPencil.mixer,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hr,flatten,components_mul]
  rfl

theorem blockMatrix_pow_mulVec (A : Pattern m → Matrix (ClockPos m) (ClockPos m) (Coeff K m))
    (β : Pattern m) (x : Fin (width m) → Coeff K m) (n : ℕ) :
    (fun v => (blockMatrix A ^ n *ᵥ x) (rowEquiv m (β,v))) =
      A β ^ n *ᵥ (fun v => x (rowEquiv m (β,v))) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ',← mulVec_mulVec,← mulVec_mulVec,← ih]
    exact funext (fun v => blockMatrix_mulVec A β v _)

@[simp] theorem flattenMatrix_pow_mulVec [Fintype I] [DecidableEq I] (A : Matrix I I (Coeff K m))
    (n : ℕ) (x : I → Coeff K m) :
    flattenMatrix A ^ n *ᵥ flatten x = flatten (A ^ n *ᵥ x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',pow_succ',← mulVec_mulVec,← mulVec_mulVec,ih,flattenMatrix_mulVec]

theorem flatten_add (x y : I → Coeff K m) : flatten (x+y) = flatten x + flatten y :=
  (flatEquiv K I m).map_add _ _

theorem flatten_sub (x y : I → Coeff K m) : flatten (x-y) = flatten x - flatten y :=
  map_sub (flatEquiv K I m) _ _

theorem flatten_smul (a : K) (x : I → Coeff K m) : flatten (a • x) = a • flatten x :=
  (flatEquiv K I m).map_smul _ _

theorem flatten_sum {N : Type} [Fintype N] (x : N → I → Coeff K m) :
    flatten (∑ i, x i) = ∑ i, flatten (x i) :=
  map_sum (flatEquiv K I m) x _

def signPattern (η : Fin m → Bool) : Pattern m := fun j => if η j then 1 else 0

def evaluated (e : Environment K m) (η : Fin m → Bool) (β : Pattern m) :
    Matrix (ClockPos m) (ClockPos m) (Coeff K m) :=
  (e.pencil.L β).map (MvPolynomial.eval (queryPowerValues e.root (signPattern η)))

theorem evaluated_eq (e : Environment K m) (η : Fin m → Bool) (β : Pattern m) :
    evaluated e η β = e.pencil.A₀ β +
      ∑ j, (if η j then (-1 : K) else 1) • e.pencil.A β j 1 := by
  classical
  have hn : (Finset.univ : Finset (ZMod 2)).erase 0 = {1} := by decide
  rw [evaluated,e.pencil.stage]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hn,Finset.sum_singleton]
  cases h : η j <;> simp [queryPowerValues, signPattern, h, digitPhase_apply, ZMod.val_one_eq_one_mod]

/-- The ordinary stored constant and query matrices specialize to precisely the
matrix of the polynomial pencil over the extension. -/
theorem signed_eq (e : Environment K m) (η : Fin m → Bool) :
    mixerMatrix e.pencil.A₀ + (∑ j, (if η j then (-1 : K) else 1) •
      mixerMatrix (fun β => e.pencil.A β j 1)) = mixerMatrix (evaluated e η) := by
  classical
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨x,rfl⟩ := (flatEquiv K (Fin (width m)) m).surjective v
  change _ *ᵥ flatten x = _ *ᵥ flatten x
  simp only [add_mulVec,sum_mulVec,smul_mulVec,mixerMatrix,flattenMatrix_mulVec,
    ← flatten_smul,← flatten_sum,← flatten_add]
  apply congrArg flatten
  funext i
  obtain ⟨⟨β,u⟩,rfl⟩ := (rowEquiv m).surjective i
  simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,blockMatrix_mulVec,evaluated_eq,
    add_mulVec,sum_mulVec,smul_mulVec]

def predictor (e : Environment K m) (η : Fin m → Bool) (i : Fin (width m)) : Coeff K m :=
  countPredictorEigenvalue (B := order m ^ clock m) e.root (signPattern η) i

set_option maxHeartbeats 1500000 in
theorem evaluated_pow_mulVec (e : Environment K m) (η : Fin m → Bool) (x : Fin (width m) → Coeff K m) :
    mixerMatrix (evaluated e η) ^ order m *ᵥ flatten x = flatten (predictor e η * x) := by
  rw [mixerMatrix,flattenMatrix_pow_mulVec]
  apply congrArg flatten
  funext i
  obtain ⟨⟨β,u⟩,rfl⟩ := (rowEquiv m).surjective i
  have h := congrFun (blockMatrix_pow_mulVec (evaluated e η) β x (order m)) u
  rw [evaluated,specialize_matrix_root _ (e.pencil.power β),smul_mulVec,one_mulVec] at h
  have hidx : ((shiftRowEquivFin 2 m (order m ^ clock m)).symm (rowEquiv m (β,u))).1 = β := by
    let c : ClockPos m ≃ Fin (order m ^ clock m) := Fintype.equivFinOfCardEq (by simp [ClockPos])
    exact congrArg Prod.fst ((shiftRowEquivFin 2 m (order m ^ clock m)).symm_apply_apply (β,c u))
  simpa only [predictor,countPredictorEigenvalue,hidx,Pi.mul_apply,Pi.smul_apply,smul_eq_mul] using h

end InterchangeROMRepair.Lower

end

end NearSquareRoot
end Computability
end OAI
