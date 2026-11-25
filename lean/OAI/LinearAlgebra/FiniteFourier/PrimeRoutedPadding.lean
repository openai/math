import OAI.LinearAlgebra.FiniteFourier.PrimeTemplate

/-! # Extending a rectangle circuit to the complete row bank

Restricting the input wires to a rectangle uses a free readout. A second
readout scales its outputs by the rectangle weight and fills all other
destinations with zero. Both preserve the local and Fourier call counts.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped Classical

variable {K : Type*} [CommSemiring K] {ℓ f F : ℕ} {ζ : K}

/-- The local register indexed by its incident label, row, and array coordinate. -/
abbrev RectangleRegister {L : Type} (S : Set L) (W X : Type) := ((↥S × W) × X)

/-- Forget the proof that a register belongs to a rectangle. -/
def rectangleRegisterVal {L W X : Type} {S : Set L}
    (k : RectangleRegister S W X) : (L × W) × X := ((k.1.1.val, k.1.2), k.2)

private theorem rectangleRegisterVal_injective {L W X : Type} {S : Set L} :
    Function.Injective (@rectangleRegisterVal L W X S) := by
  rintro ⟨⟨⟨v, hv⟩, u⟩, x⟩ ⟨⟨⟨w, hw⟩, t⟩, y⟩ e
  simpa [rectangleRegisterVal] using e

/-- Zero outside the rectangle, and the given block times its weight inside. -/
def routedRectangleMatrix {L W X : Type} (S T : Set L) (z : K)
    (B : Matrix ((L × W) × X) ((L × W) × X) K) :
    Matrix ((L × W) × X) ((L × W) × X) K :=
  fun o i => if i.1.1 ∈ S ∧ o.1.1 ∈ T then z * B o i else 0

/-- A program for the restricted transfer extends to the full bank with the same costs. -/
theorem PrimeTemplateProgram.rectangle {L W X : Type} [Fintype L] [Fintype W] [Fintype X]
    (S T : Set L) (z : K) (B : Matrix ((L × W) × X) ((L × W) × X) K) {c s : ℕ}
    (p : PrimeTemplateProgram ℓ f F ζ
      (B.submatrix (@rectangleRegisterVal L W X T) (@rectangleRegisterVal L W X S)) c s) :
    PrimeTemplateProgram ℓ f F ζ (routedRectangleMatrix S T z B) c s := by
  classical
  let pick : Matrix (RectangleRegister S W X) ((L × W) × X) K :=
    fun o i => if i = rectangleRegisterVal o then 1 else 0
  let write : Matrix ((L × W) × X) (RectangleRegister T W X) K :=
    fun o i => if rectangleRegisterVal i = o then z else 0
  have hPick : RealizableAtMost pick 0 := by
    refine ⟨0, le_rfl, ⟨.nil, fun k => .scaled 1 (.inl (rectangleRegisterVal k))⟩, ?_⟩
    ext o i
    simp [pick, Circuit.matrix, Circuit.eval, Readout.eval, Pi.single_apply, eq_comm]
  have hWrite : RealizableAtMost write 0 := by
    refine ⟨0, le_rfl, ⟨.nil, fun k => if h : k.1.1 ∈ T then
      .scaled z (.inl ((⟨k.1.1, h⟩, k.1.2), k.2)) else .zero⟩, ?_⟩
    ext ⟨⟨w,u⟩,y⟩ ⟨⟨⟨v,hv⟩,t⟩,x⟩
    by_cases hw : w ∈ T
    · simp [write, Circuit.matrix, Circuit.eval, Readout.eval, Pi.single_apply, hw,
        rectangleRegisterVal, mul_ite, eq_comm]
    · have hn : v ≠ w := fun h => hw (h ▸ hv)
      simp [write, Circuit.matrix, Circuit.eval, Readout.eval, hw, rectangleRegisterVal, hn]
  have hp := (PrimeTemplateProgram.localCircuit hWrite).serial (p.serial (.localCircuit hPick))
  convert hp using 1
  · ext ⟨⟨w,u⟩,y⟩ ⟨⟨v,t⟩,x⟩
    rw [Matrix.mul_apply]
    simp only [pick, write, ite_mul, zero_mul, routedRectangleMatrix]
    by_cases hw : w ∈ T
    · let o : RectangleRegister T W X := ((⟨w, hw⟩, u), y)
      have ho (k : RectangleRegister T W X) :
          rectangleRegisterVal k = ((w,u),y) ↔ k = o :=
        (@rectangleRegisterVal_injective L W X T).eq_iff (a := k) (b := o)
      simp only [ho, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hw, and_true]
      change _ = z * ∑ k : RectangleRegister S W X, B (rectangleRegisterVal o) (rectangleRegisterVal k) * (if ((v,t),x) = rectangleRegisterVal k then 1 else 0)
      simp only [mul_ite, mul_one, mul_zero]
      by_cases hv : v ∈ S
      · let i : RectangleRegister S W X := ((⟨v,hv⟩,t),x)
        have hi (k : RectangleRegister S W X) :
            ((v,t),x) = rectangleRegisterVal k ↔ i = k :=
          (@rectangleRegisterVal_injective L W X S).eq_iff (a := i) (b := k)
        simp only [hv, hi, ite_true, Finset.sum_ite_eq, Finset.mem_univ]
        rfl
      · have hi (k : RectangleRegister S W X) : ((v,t),x) ≠ rectangleRegisterVal k :=
          fun he => hv ((show k.1.1.val = v from (congrArg (fun z : (L × W) × X => z.1.1) he).symm) ▸ k.1.1.property)
        simp [hv, hi]
    · have ho (k : RectangleRegister T W X) : rectangleRegisterVal k ≠ ((w,u),y) :=
        fun he => hw ((show k.1.1.val = w from congrArg (fun z : (L × W) × X => z.1.1) he) ▸ k.1.1.property)
      simp [hw, ho]
  · simp
  · simp

end

end

end FiniteFourier
end LinearAlgebra
end OAI
