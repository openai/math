import OAI.Computability.NearSquareRoot.KernelPassAxes
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # From operations on one address column to a single fixed stream program

A binary reindexing on all columns is implemented by the XOR word for the single
column matrix. A product of fixed signs over the columns is a one-bit selector.
The lift of a product of ordinary column matrices is the product of their lifts,
including on the empty address. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Finset Matrix SynchronizedPadding

abbrev Bits (A : ℕ) := Fin A → ZMod 2
abbrev Local (A : ℕ) := Matrix (Bits A) (Bits A) ℂ
variable {A : ℕ}

/-- Expose both bits of each pair as separate column letters. -/
def expose (h : ℕ) : Addr A h ≃ (Fin h × Fin 2 → Bits A) where
  toFun u t a := u t.1 a t.2
  invFun v i a j := v (i,j) a
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def lift (h : ℕ) (M : Local A) : Matrix (Addr A h) (Addr A h) ℂ :=
  (tensorMatrix fun _ : Fin h × Fin 2 => M).submatrix (expose h) (expose h)

theorem lift_mul (h : ℕ) (M N : Local A) : lift h (M*N) = lift h M * lift h N := by
  rw [lift, tensorMatrix_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ (expose h) _).symm

@[simp] theorem lift_one (h : ℕ) : lift h (1 : Local A) = 1 := by
  simp [lift, Matrix.submatrix_one_equiv]

/-- A single program implements all paired-column widths. -/
def Implements (p : Plan A 1 1) (M : Local A) : Prop :=
  ∀ h, (oneRow (p.eval h)).map (algebraMap ℚ ℂ) = lift h M

theorem Implements.seq {p q : Plan A 1 1} {M N : Local A} (hp : Implements p M)
    (hq : Implements q N) : Implements (p.seq q) (M*N) := by
  intro h
  change (oneRow (p.eval h * q.eval h)).map _ = _
  rw [oneRow_mul, Matrix.map_mul, hp h, hq h, lift_mul]

theorem implements_identity : Implements (identity (A := A)) 1 := by
  intro h
  rw [lift_one]
  ext y x
  change (algebraMap ℚ ℂ) (if x = y then value (1,0) else 0) = _
  by_cases e : x = y
  · subst x; simp [value]
  · simp [e, Ne.symm e]

/-- Matrix of a forward reindexing, with output address first. -/
def pushAddress (u : Bits A → Bits A) : Local A := fun y x => if y = u x then 1 else 0

theorem pushAddress_comp (g f : Bits A → Bits A) :
    pushAddress (g ∘ f) = pushAddress g * pushAddress f := by
  ext y x
  simp [pushAddress, Matrix.mul_apply]

private theorem lift_push (h : ℕ) (u : Bits A → Bits A) (y x : Addr A h) :
    lift h (pushAddress u) y x =
      if expose h y = u ∘ expose h x then 1 else 0 := by
  change (∏ t, if expose h y t = u (expose h x t) then (1 : ℂ) else 0) = _
  by_cases e : expose h y = u ∘ expose h x
  · simp [e]
  · obtain ⟨t,ht⟩ := Function.ne_iff.mp e
    simp only [e, ↓reduceIte]
    exact prod_eq_zero (mem_univ t) (by simpa [Function.comp_apply] using ht)

theorem implements_xor (g : Fin A × Fin A) :
    Implements (Plan.xor g) (pushAddress (KernelColumn.gateMatrix g).mulVec) := by
  intro h
  ext y x
  rw [lift_push]
  have eqv : expose h y = (KernelColumn.gateMatrix g).mulVec ∘ expose h x ↔
      y = xorColumn g ∘ x := by
    have E : expose h (xorColumn g ∘ x) = (KernelColumn.gateMatrix g).mulVec ∘ expose h x := by
      funext ⟨c,t⟩ a
      let v : KernelColumn.Address A h 2 := fun a c t => x c a t
      simpa [expose, xorColumn, KernelColumn.pass, v] using
        congrFun (KernelColumn.pass_at g t v c) a
    rw [← E]
    exact (expose h).injective.eq_iff
  change (algebraMap ℚ ℂ) (if y = xorColumn g ∘ x then 1 else 0) = _
  simp only [eqv]
  split <;> simp

def reindexWord (w : KernelColumn.Word A) : Plan A 1 1 :=
  w.foldr (fun g tail => .seq (.xor g) tail) identity

theorem calls_reindexWord (w : KernelColumn.Word A) : (reindexWord w).calls = 0 := by
  induction w with
  | nil => rfl
  | cons g w ih => change 0 + (reindexWord w).calls = _; omega

theorem implements_reindexWord (w : KernelColumn.Word A) :
    Implements (reindexWord w) (pushAddress (KernelColumn.wordMatrix w).mulVec) := by
  induction w with
  | nil =>
    have he : pushAddress (KernelColumn.wordMatrix ([] : KernelColumn.Word A)).mulVec = 1 := by
      ext y x
      change (if y = (1 : KernelColumn.BinaryMatrix A).mulVec x then (1 : ℂ) else 0) = _
      simp [Matrix.one_apply]
    rw [he]
    exact implements_identity
  | cons g w ih =>
    have he : (KernelColumn.wordMatrix (g::w)).mulVec =
        (KernelColumn.gateMatrix g).mulVec ∘ (KernelColumn.wordMatrix w).mulVec :=
      funext (fun x => (Matrix.mulVec_mulVec x _ _).symm)
    rw [he, pushAddress_comp]
    exact (implements_xor g).seq ih

/-- Simultaneously implement a coordinate change, with no child calls. -/
theorem reindex_linear (e : Bits A ≃ₗ[ZMod 2] Bits A) :
    ∃ p : Plan A 1 1, p.calls = 0 ∧ Implements p (pushAddress e) := by
  let M := e.toLinearMap.toMatrix'
  have hM : M.det ≠ 0 := by
    apply IsUnit.ne_zero
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply LinearMap.isUnit_toMatrix'_iff.mpr
    exact ⟨⟨e.toLinearMap, e.symm.toLinearMap, by ext; simp, by ext; simp⟩, rfl⟩
  let w := KernelColumn.compile M hM
  refine ⟨reindexWord w, calls_reindexWord _, ?_⟩
  have hs := implements_reindexWord w
  have hm : KernelColumn.wordMatrix w = M := KernelColumn.wordMatrix_compile _ _
  rw [hm] at hs
  have E : M.mulVec = ⇑e := funext (fun x => LinearMap.toMatrix'_mulVec _ _)
  simpa only [E] using hs

end KernelPass

end NearSquareRoot
end Computability
end OAI
