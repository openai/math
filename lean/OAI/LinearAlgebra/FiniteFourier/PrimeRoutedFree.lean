import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateProgram.PrimeRoutedBlocks
import OAI.LinearAlgebra.FiniteFourier.CircuitRingCombine

/-! # Sharing endpoint transforms in a free routing rectangle

All source rows are converted once, followed by the local middle operators,
then all target rows are converted once. The local circuit bound is uniform
in the number of coordinates per row.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Matrix
open scoped Classical
noncomputable section

variable {K : Type*} [CommSemiring K]

/-- Insert one operator between two selected rows, with zero blocks elsewhere. -/
private def singleRowBlock {I O X : Type} (o : O) (i : I) (M : Matrix X X K) :
    Matrix (O × X) (I × X) K :=
  of fun u v => if u.1 = o ∧ v.1 = i then M u.2 v.2 else 0

private theorem singleRowBlock_cost {I O X : Type} [Fintype X] (o : O) (i : I) {M : Matrix X X K}
    {c : ℕ} (h : RealizableAtMost M c) : RealizableAtMost (singleRowBlock o i M) c := by
  obtain ⟨n, hn, p, rfl⟩ := h
  let q := p.rewire (fun x => (1, (i,x))) (fun x => (1,x))
  let r : Circuit K (I × X) (O × X) n :=
    ⟨q.program, fun u => if u.1 = o then q.output u.2 else .zero⟩
  refine ⟨n, hn, r, ?_⟩
  ext ⟨t,x⟩ ⟨s,y⟩
  rw [Circuit.matrix_apply]
  by_cases ht : t = o
  · subst t
    change (if o = o then q.output x else Readout.zero).eval _ = _
    rw [ite_eq_left rfl]
    change q.eval (Pi.single (s,y) 1) x = _
    rw [Circuit.eval_rewire]
    by_cases hs : s = i
    · subst s
      simp [Pi.single_apply, singleRowBlock, Circuit.matrix]
      congr 1
      ext a
      simp [Pi.single_apply]
    · simp [singleRowBlock, hs, Ne.symm hs, Circuit.eval_eq_mulVec, Matrix.mulVec, dotProduct]
  · simp [singleRowBlock, Circuit.matrix, Circuit.eval, r, ht, Readout.eval]

private theorem sum_matrix_cost {I O U : Type} [Fintype O] (M : U → Matrix O I K)
    (t : Finset U) {c : ℕ} (h : ∀ u, RealizableAtMost (M u) c) :
    RealizableAtMost (∑ u ∈ t, M u) (t.card * (c + Fintype.card O)) := by
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨0, Nat.zero_le _, ⟨.nil, fun _ => .zero⟩, by ext; simp [Circuit.matrix, Circuit.eval, Readout.eval]⟩
  | @insert u t hu ih =>
    obtain ⟨n, hn, p, hp⟩ := h u
    obtain ⟨m, hm, q, hq⟩ := ih
    obtain ⟨l, hl, r, hr⟩ := circuit_sumPair I O (1 : K) 1 p q
    refine ⟨l, ?_, r, ?_⟩
    · rw [card_insert_of_notMem hu, Nat.succ_mul]
      omega
    · rw [sum_insert hu, ← hp, ← hq]
      ext o i
      simpa [Circuit.matrix] using hr (Pi.single i 1) o

/-- All `J` middle terms are local linear circuits between a pair of rows.
Inserting and summing their independent circuits costs linearly in the row size. -/
theorem routedMiddle_cost {I O J X : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype X]
    (M : O → I → J → Matrix X X K) (D : ℕ)
    (h : ∀ o i j, RealizableAtMost (M o i j) (D * Fintype.card X)) :
    RealizableAtMost (of fun (u : O × X) (v : I × X) => ∑ j, M u.1 v.1 j u.2 v.2)
      ((Fintype.card O * Fintype.card I * Fintype.card J * (D + Fintype.card O)) * Fintype.card X) := by
  let U := O × I × J
  let N (k : U) := singleRowBlock k.1 k.2.1 (M k.1 k.2.1 k.2.2)
  have hn := sum_matrix_cost N univ (fun (k : U) => singleRowBlock_cost k.1 k.2.1 (h _ _ _))
  have heq : (∑ k, N k) = of fun (u : O × X) (v : I × X) => ∑ j, M u.1 v.1 j u.2 v.2 := by
    ext ⟨o,x⟩ ⟨i,y⟩
    simp [U, Fintype.sum_prod_type, N, singleRowBlock, Matrix.sum_apply, ite_and]
  rw [heq] at hn
  convert hn using 1
  simp [U, Fintype.card_prod]
  ring

/-- Matrix sent by one rectangle. The endpoint transforms depend only on their
own label and are shared across all middle terms and opposite endpoints. -/
def freeRectangleMatrix {S T W J X : Type} [Fintype J] [Fintype X]
    (B : J → Matrix W W K) (Eout : T → Matrix X X K) (Mid : J → T → S → Matrix X X K)
    (Ein : S → Matrix X X K) : Matrix ((T × W) × X) ((S × W) × X) K :=
  of fun u v => ∑ j, B j u.1.2 v.1.2 * (Eout u.1.1 * Mid j u.1.1 v.1.1 * Ein v.1.1) u.2 v.2


/-- Flatten a matrix of equal-size blocks, placing the row label first. -/
private def rowBlocks {I O X : Type} (M : O → I → Matrix X X K) :
    Matrix (O × X) (I × X) K := of fun u v => M u.1 v.1 u.2 v.2

/-- An independent family of operators on the rows in row-first order. -/
private def independentRows {I X : Type} (M : I → Matrix X X K) :
    Matrix (I × X) (I × X) K :=
  of fun u v => if u.1 = v.1 then M u.1 u.2 v.2 else 0

private theorem rowBlocks_mul_independentRows {I O X : Type} [Fintype I] [Fintype X]
    (A : O → I → Matrix X X K) (B : I → Matrix X X K) :
    rowBlocks A * independentRows B = rowBlocks (fun o i => A o i * B i) := by
  ext ⟨o,x⟩ ⟨i,y⟩
  simp [rowBlocks, independentRows, Matrix.mul_apply, Fintype.sum_prod_type,
    mul_ite]

private theorem independentRows_mul_rowBlocks {I O X : Type} [Fintype O] [Fintype X]
    (A : O → Matrix X X K) (B : O → I → Matrix X X K) :
    independentRows A * rowBlocks B = rowBlocks (fun o i => A o * B o i) := by
  ext ⟨o,x⟩ ⟨i,y⟩
  simp [rowBlocks, independentRows, Matrix.mul_apply, Fintype.sum_prod_type,
    ite_mul]

private theorem freeRectangleMatrix_factor {S T W J X : Type}
    [Fintype S] [Fintype T] [Fintype W] [Fintype J] [Fintype X]
    (B : J → Matrix W W K) (Eout : T → Matrix X X K) (Mid : J → T → S → Matrix X X K)
    (Ein : S → Matrix X X K) :
    freeRectangleMatrix B Eout Mid Ein =
      independentRows (fun o : T × W => Eout o.1) *
      rowBlocks (fun (o : T × W) (i : S × W) => ∑ j, B j o.2 i.2 • Mid j o.1 i.1) *
      independentRows (fun i : S × W => Ein i.1) := by
  rw [independentRows_mul_rowBlocks, rowBlocks_mul_independentRows]
  ext ⟨⟨t,u⟩,x⟩ ⟨⟨s,v⟩,y⟩
  simp [freeRectangleMatrix, rowBlocks, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]


private theorem independentRows_program {ℓ f F : ℕ} {ζ : K} {A W X : Type}
    [Fintype A] [Fintype W] [Fintype X] (E : A → Matrix X X K) {c s : A → ℕ}
    (p : ∀ a, PrimeTemplateProgram ℓ f F ζ (E a) (c a) (s a)) :
    PrimeTemplateProgram ℓ f F ζ (independentRows (fun i : A × W => E i.1))
      (Fintype.card W * ∑ a, c a) (Fintype.card W * ∑ a, s a) := by
  classical
  have h := ((PrimeTemplateProgram.blockDiagonal (fun i : A × W => p i.1))).reindex
    (Equiv.prodComm X (A × W)) (Equiv.prodComm X (A × W))
  convert h using 1
  · ext ⟨i,x⟩ ⟨j,y⟩
    by_cases hi : i = j <;> simp [independentRows, Matrix.reindex_apply, Matrix.blockDiagonal_apply, hi]
  · simp [Fintype.sum_prod_type, Finset.mul_sum]
  · simp [Fintype.sum_prod_type, Finset.mul_sum]

/-- Compiling a free rectangle charges each endpoint once for each clock row.
The remaining cost is linear in the coordinate count, uniformly over all
coordinate sets and all input, output, and middle matrices. -/
theorem freeRectangleMatrix_program {ℓ f F : ℕ} {ζ : K} {S T W J X : Type}
    [Fintype S] [Fintype T] [Fintype W] [Fintype J] [Fintype X]
    (B : J → Matrix W W K) (Eout : T → Matrix X X K) (Mid : J → T → S → Matrix X X K)
    (Ein : S → Matrix X X K) {co so : T → ℕ} {ci si : S → ℕ} (D : ℕ)
    (po : ∀ t, PrimeTemplateProgram ℓ f F ζ (Eout t) (co t) (so t))
    (pm : ∀ j t s, RealizableAtMost (Mid j t s) (D * Fintype.card X))
    (pi : ∀ s, PrimeTemplateProgram ℓ f F ζ (Ein s) (ci s) (si s)) :
    PrimeTemplateProgram ℓ f F ζ (freeRectangleMatrix B Eout Mid Ein)
      (Fintype.card W * ((∑ t, co t) + ∑ s, ci s) +
        (Fintype.card (T × W) * Fintype.card (S × W) * Fintype.card J *
          (D + Fintype.card (T × W))) * Fintype.card X)
      (Fintype.card W * ((∑ t, so t) + ∑ s, si s)) := by
  have hm := routedMiddle_cost (fun (o : T × W) (i : S × W) j => B j o.2 i.2 • Mid j o.1 i.1)
    D (fun o i j => (pm j o.1 i.1).smul _)
  have h := ((independentRows_program (W := W) Eout po).serial
    (.localCircuit hm)).serial (independentRows_program (W := W) Ein pi)
  rw [freeRectangleMatrix_factor]
  convert h using 1
  · congr 2
    ext ⟨o,x⟩ ⟨i,y⟩
    simp [rowBlocks, Matrix.sum_apply]
  · ring
  · ring

end

end FiniteFourier
end LinearAlgebra
end OAI
