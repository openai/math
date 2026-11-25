import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedCharged
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedFree
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedPadding

/-! # Rectangle programs on the full routing-label bank

The coefficient matrix acts on the clock rows. Each pair of labels supplies
a coordinate transfer. A rectangle factorization needs to agree with these
transfers only on its own source and target labels.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix Finset
open scoped Classical

variable {K : Type*} [CommSemiring K] {ℓ f F : ℕ} {ζ : K}
variable {L W J X : Type} [Fintype L] [Fintype W] [Fintype X]

/-- One term in a routed pencil, with the target label first in the transfer kernel. -/
def routedPencilTerm (B : Matrix W W K) (H : L → L → Matrix X X K) :
    Matrix ((L × W) × X) ((L × W) × X) K :=
  of fun o i => B o.1.2 i.1.2 * H o.1.1 i.1.1 o.2 i.2

/-- Uniform coefficient of the local gate count for one charged rectangle. -/
def chargedRectangleOverhead (nS nT nW cPre cPost cMid : ℕ) : ℕ :=
  nW * (nS * cPre + nT * cPost + nS * nW + cMid)

/-- A common middle transform is charged only once per clock row for the
whole rectangle, including all scalar row mixing and extension by zero. -/
theorem routedChargedRectangle_program (S T : Set L) (z : K) (B : Matrix W W K)
    (H : L → L → Matrix X X K) (post : T → Matrix X X K) (M : Matrix X X K)
    (pre : S → Matrix X X K)
    (hfac : ∀ (t : T) (s : S), H t s = post t * M * pre s)
    (cPre cPost cMid : ℕ) {c s : ℕ}
    (hpost : ∀ t, RealizableAtMost (post t) (cPost * Fintype.card X))
    (hpre : ∀ i, RealizableAtMost (pre i) (cPre * Fintype.card X))
    (hm : PrimeTemplateProgram ℓ f F ζ M c s) (hc : c ≤ cMid * Fintype.card X) :
    ∃ n ≤ chargedRectangleOverhead (Fintype.card S) (Fintype.card T) (Fintype.card W)
        cPre cPost cMid * Fintype.card X,
      PrimeTemplateProgram ℓ f F ζ (routedRectangleMatrix S T z (routedPencilTerm B H)) n
        (Fintype.card W * s) := by
  have p := chargedRectangle_template B post pre hpost hpre hm
  have he : (routedPencilTerm B H).submatrix rectangleRegisterVal rectangleRegisterVal =
      chargedRectangleMatrix B post M pre := by
    ext ⟨⟨t,u⟩,x⟩ ⟨⟨s,v⟩,y⟩
    simp [routedPencilTerm, rectangleRegisterVal, chargedRectangleMatrix, hfac]
  rw [← he] at p
  refine ⟨_, ?_, PrimeTemplateProgram.rectangle S T z _ p⟩
  refine (Nat.add_le_add_left (Nat.mul_le_mul_left (Fintype.card W) hc) _).trans ?_
  apply le_of_eq
  unfold chargedRectangleOverhead
  ring

/-- Uniform coefficient of the local gate count for one free rectangle. -/
def freeRectangleOverhead (nS nT nW nJ cPre cPost cMid : ℕ) : ℕ :=
  nW * (nT * cPost + nS * cPre) + (nT*nW) * (nS*nW) * nJ * (cMid + nT*nW)

/-- Sharing both endpoint families implements all terms together, with a
local cost coefficient independent of the coordinate set and coefficient matrices. -/
theorem routedFreeRectangle_program [Fintype J] (S T : Set L) (z : K) (B : J → Matrix W W K)
    (H : J → L → L → Matrix X X K) (post : T → Matrix X X K)
    (Mid : J → T → S → Matrix X X K) (pre : S → Matrix X X K)
    (hfac : ∀ j (t : T) (s : S), H j t s = post t * Mid j t s * pre s)
    (cPre cPost cMid : ℕ) {co so : T → ℕ} {ci si : S → ℕ}
    (hpost : ∀ t, PrimeTemplateProgram ℓ f F ζ (post t) (co t) (so t))
    (hco : ∀ t, co t ≤ cPost * Fintype.card X)
    (hm : ∀ j t s, RealizableAtMost (Mid j t s) (cMid * Fintype.card X))
    (hpre : ∀ s, PrimeTemplateProgram ℓ f F ζ (pre s) (ci s) (si s))
    (hci : ∀ s, ci s ≤ cPre * Fintype.card X) :
    ∃ n ≤ freeRectangleOverhead (Fintype.card S) (Fintype.card T) (Fintype.card W)
        (Fintype.card J) cPre cPost cMid * Fintype.card X,
      PrimeTemplateProgram ℓ f F ζ
        (routedRectangleMatrix S T z (∑ j, routedPencilTerm (B j) (H j))) n
        (Fintype.card W * ((∑ t, so t) + ∑ s, si s)) := by
  have p := freeRectangleMatrix_program B post Mid pre cMid hpost hm hpre
  have ho : ∑ t, co t ≤ Fintype.card T * (cPost * Fintype.card X) := by
    simpa using sum_le_sum (s := univ) (fun t _ => hco t)
  have hi : ∑ s, ci s ≤ Fintype.card S * (cPre * Fintype.card X) := by
    simpa using sum_le_sum (s := univ) (fun s _ => hci s)
  have he : (∑ j, routedPencilTerm (B j) (H j)).submatrix rectangleRegisterVal rectangleRegisterVal =
      freeRectangleMatrix B post Mid pre := by
    ext ⟨⟨t,u⟩,x⟩ ⟨⟨s,v⟩,y⟩
    simp [routedPencilTerm, rectangleRegisterVal, freeRectangleMatrix, Matrix.sum_apply, hfac]
  rw [← he] at p
  refine ⟨_, ?_, PrimeTemplateProgram.rectangle S T z _ p⟩
  refine (Nat.add_le_add_right (Nat.mul_le_mul_left (Fintype.card W) (Nat.add_le_add ho hi)) _).trans ?_
  apply le_of_eq
  simp only [freeRectangleOverhead, Fintype.card_prod]
  ring

end

end

end FiniteFourier
end LinearAlgebra
end OAI
