import OAI.Computability.NearSquareRoot.KernelBinaryQueryLift
import OAI.Computability.NearSquareRoot.KernelPassLabelRepair

/-! # Restoring the normalized Walsh transform after the binary query product -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Plan

open Matrix Finset PencilSearch PencilDescent BinaryQuery

variable {A h n m u N : ℕ} {L : Type*}

theorem applyAt_one_perRow (p : Plan A 1 1) (x : Bank A h n) (b : Fin n) :
    (perRow (fun _ => p)).applyAt h x b = oneRow (p.eval h) *ᵥ x b := by
  rw [applyAt_perRow]
  funext y
  simp [applyAt, oneRow, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem correct_of_row_action (p : Plan A n n)
    (hp : ∀ h (x : Bank A h n) (i : Fin n), p.applyAt h x i = walshMatrix A h *ᵥ x i) :
    Correct p := by
  intro h
  apply eval_eq_of_applyAt
  intro x
  funext i y
  rw [hp]
  simp [target, walshMatrix, columnWalsh, pairWalsh, SynchronizedPadding.tensorMatrix,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]
  rw [Finset.sum_comm]
  simp

def wrap (front back : Plan A 1 1) (p : Plan A n n) : Plan A n n :=
  ((perRow (fun _ => back)).seq p).seq (perRow fun _ => front)

@[simp] theorem calls_wrap (front back : Plan A 1 1) (p : Plan A n n)
    (hf : front.calls = 0) (hb : back.calls = 0) : (wrap front back p).calls = p.calls := by
  simp [wrap, calls, hf, hb]

/-- Correctness under correction passes follows from their product with the
ordinary kernel of the middle program. -/
theorem correct_wrap (front back : Plan A 1 1) (p : Plan A n n)
    (U : (h : ℕ) → Matrix (Addr A h) (Addr A h) ℚ)
    (hp : ∀ h (x : Bank A h n) (i : Fin n), p.applyAt h x i = U h *ᵥ x i)
    (hu : ∀ h, oneRow (back.eval h) * U h * oneRow (front.eval h) = walshMatrix A h) :
    Correct (wrap front back p) := by
  apply correct_of_row_action
  intro h x i
  rw [wrap, applyAt_seq, applyAt_seq, applyAt_one_perRow, hp, applyAt_one_perRow,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]

/-- Conjugating a frequency multiplier by the rational Walsh involution is its
ordinary-coordinate action. -/
def fromMultiplier {A h : ℕ} (r : Addr A h → ℚ) : Matrix (Addr A h) (Addr A h) ℚ :=
  walshMatrix A h * diagonal r * walshMatrix A h

theorem mulVec_fromMultiplier {W : ℕ} (r : Addr A h → ℚ) (x z : Bank A h W) (b : Fin W)
    (hz : ∀ y, frequency z b y = r y * frequency x b y) :
    z b = fromMultiplier r *ᵥ x b := by
  have he : walshMatrix A h *ᵥ z b = diagonal r *ᵥ (walshMatrix A h *ᵥ x b) := by
    funext y
    rw [Matrix.mulVec_diagonal]
    exact hz y
  calc
    z b = walshMatrix A h *ᵥ (walshMatrix A h *ᵥ z b) := by
      rw [Matrix.mulVec_mulVec, walshMatrix_mul_self, Matrix.one_mulVec]
    _ = fromMultiplier r *ᵥ x b := by rw [he, fromMultiplier, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- The compiled repair product on an arbitrary physically numbered row. -/
theorem compiledLabelBatch_mulVec (hm : 2 ≤ m) (e : L ≃ Fin N) (test : Column A → Signature m)
    (p : Plan A (N*basisWidth m) (N*basisWidth m))
    (hp : ∀ v (x : Bank A h (N*basisWidth m)) (y : Addr A h),
      labelSlice e v y (p.applyAt h x) = stageMatrix hm (∑ j, test (y j)) *ᵥ labelSlice e v y x)
    (x : Bank A h (N*basisWidth m)) (i : Fin (N*basisWidth m)) :
    (compiledLabelBatch hm e (fun _ => test) p).applyAt h x i =
      fromMultiplier (fun y => ∏ j, (-1 : ℚ)^((∑ c, test (y c)) j).val) *ᵥ x i := by
  apply mulVec_fromMultiplier
  obtain ⟨⟨v,b⟩,rfl⟩ := (groupIndex e _).surjective i
  obtain ⟨j,rfl⟩ := (finProdFinEquiv (m := batchWidth m) (n := 2 ^ batchExponent m)).surjective b
  intro y
  exact congrFun (frequency_compiledLabelBatch hm e (fun _ => test) p hp v x y) j

/-- Lift the ordinary-kernel correction identity separately to all paired
columns, using injectivity of rational-to-complex scalar extension. -/
theorem outer_kernel {m u : ℕ} (hm : m ≡ 1 [MOD 2])
    (front back : Plan (Arity m u) 1 1)
    (hf : Implements front (chirp m u))
    (hb : Implements back (pushAddress (swapHalves m u) * chirp m u))
    (M : Matrix (Addr (Arity m u) h) (Addr (Arity m u) h) ℚ)
    (hM : M.map (algebraMap ℚ ℂ) = lift h (List.ofFn (query (m:=m) (u:=u))).prod) :
    oneRow (back.eval h) * M * oneRow (front.eval h) = walshMatrix (Arity m u) h := by
  have he : (oneRow (back.eval h) * M * oneRow (front.eval h)).map (algebraMap ℚ ℂ) =
      (walshMatrix (Arity m u) h).map (algebraMap ℚ ℂ) := by
    rw [Matrix.map_mul, Matrix.map_mul, hb h, hf h, hM, ← lift_mul, ← lift_mul, ← recover hm, lift_walsh]
  ext y x
  exact (algebraMap ℚ ℂ).injective (congrFun (congrFun he y) x)

end KernelPass.Plan

end NearSquareRoot
end Computability
end OAI
