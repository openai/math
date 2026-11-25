import OAI.Computability.NearSquareRoot.InterchangeSlots
import OAI.Computability.NearSquareRoot.InterchangeSpecialization
import OAI.Computability.NearSquareRoot.InterchangeTriangular

/-!
# Address program for the query-dependent endpoint change

In coordinates for the early, main, and late fields, the endpoint map consists
of two shears. Their product has an identity diagonal. Each update reads only
its target and fields before it in physical order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Matrix IntegerMultiplication.Port

variable {K : Type*} [CommRing K] {c b e : ℕ}

/-- Concatenate the early reserve, the two main fields, and the late reserve. -/
def endpointFields {α : Type*} (x : Fin c → α) (m : Fin b → α) (z : Fin e → α) :
    Fin (c + (b + e)) → α := Fin.append x (Fin.append m z)

/-- Matrix of `(x,m,z) ↦ (x,m-Gx,z+D(m-Gx))` in physical block order. -/
def endpointMatrix (G : Matrix (Fin b) (Fin c) K) (D : Matrix (Fin e) (Fin b) K) :
    Matrix (Fin (c + (b+e))) (Fin (c + (b+e))) K :=
  Matrix.of (endpointFields
    (fun i => endpointFields ((1 : Matrix (Fin c) (Fin c) K) i) 0 0)
    (fun i => endpointFields ((-G) i) ((1 : Matrix (Fin b) (Fin b) K) i) 0)
    (fun i => endpointFields ((-(D * G)) i) (D i) ((1 : Matrix (Fin e) (Fin e) K) i)))

private theorem dot_endpointFields (u x : Fin c → K) (v m : Fin b → K) (w z : Fin e → K) :
    dotProduct (Fin.append u (Fin.append v w)) (Fin.append x (Fin.append m z)) =
      dotProduct u x + (dotProduct v m + dotProduct w z) := by
  simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem endpointMatrix_mulVec (G : Matrix (Fin b) (Fin c) K) (D : Matrix (Fin e) (Fin b) K)
    (x : Fin c → K) (m : Fin b → K) (z : Fin e → K) :
    endpointMatrix G D *ᵥ endpointFields x m z =
      endpointFields x (m - G *ᵥ x) (z + D *ᵥ (m - G *ᵥ x)) := by
  have hone {k : ℕ} (v : Fin k → K) (i : Fin k) :
      (1 : Matrix (Fin k) (Fin k) K) i ⬝ᵥ v = v i := congrFun (Matrix.one_mulVec v) i
  have hneg {s t : ℕ} (A : Matrix (Fin s) (Fin t) K) (v : Fin t → K) (i : Fin s) :
      (-A) i ⬝ᵥ v = -(A *ᵥ v) i := congrFun (Matrix.neg_mulVec v A) i
  ext i
  refine Fin.addCases (fun i => ?_) (Fin.addCases (fun i => ?_) (fun i => ?_)) i
  all_goals
    simp only [Matrix.mulVec, endpointMatrix, of_apply, endpointFields, Fin.append_left,
      Fin.append_right]
    rw [dot_endpointFields]
  · simp [hone]
  · simp [hone, hneg, sub_eq_add_neg, add_comm]
  · rw [hone, hneg, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    change -((D * G) *ᵥ x) i + ((D *ᵥ m) i + z i) =
      z i + ((D *ᵥ m) i - ((D * G) *ᵥ x) i)
    abel

theorem endpointMatrix_diagonal (G : Matrix (Fin b) (Fin c) K) (D : Matrix (Fin e) (Fin b) K)
    (i : Fin (c + (b + e))) : endpointMatrix G D i i = 1 := by
  refine Fin.addCases (fun i => ?_) (Fin.addCases (fun i => ?_) (fun i => ?_)) i <;>
    simp [endpointMatrix, endpointFields]

theorem endpointMatrix_lower (G : Matrix (Fin b) (Fin c) K) (D : Matrix (Fin e) (Fin b) K) :
    (endpointMatrix G D).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  revert hij
  revert j
  refine Fin.addCases (fun i => ?_) (Fin.addCases (fun i => ?_) (fun i => ?_)) i <;>
    intro j <;>
    refine Fin.addCases (fun j => ?_) (Fin.addCases (fun j => ?_) (fun j => ?_)) j <;>
    simp only [endpointMatrix, endpointFields, of_apply, Fin.append_left, Fin.append_right,
      Matrix.one_apply, Pi.zero_apply, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] <;>
    intros <;> (try split_ifs) <;> (try rfl) <;> (try simp_all) <;> omega

/-- The rational block formula survives specialization to any residue ring. -/
theorem endpointMatrix_token {S : Type} [CommRing S]
    {G : Matrix (Fin b) (Fin c) ℚ} {D : Matrix (Fin e) (Fin b) ℚ}
    {G' : Matrix (Fin b) (Fin c) S} {D' : Matrix (Fin e) (Fin b) S}
    (hG : MatrixToken G G') (hD : MatrixToken D D') :
    MatrixToken (endpointMatrix G D) (endpointMatrix G' D') := by
  intro i j
  revert j
  refine Fin.addCases (fun i => ?_) (Fin.addCases (fun i => ?_) (fun i => ?_)) i <;>
    intro j <;>
    refine Fin.addCases (fun j => ?_) (Fin.addCases (fun j => ?_) (fun j => ?_)) j <;>
    simp only [endpointMatrix, endpointFields, Matrix.of_apply, Fin.append_left,
      Fin.append_right, Matrix.one_apply, Pi.zero_apply, Matrix.neg_apply] <;>
    first | apply Token.zero | exact hD _ _ | exact (hG _ _).neg |
      exact ((hD.mul hG) _ _).neg | split_ifs <;> first | apply Token.unit | apply Token.zero

private theorem triangular_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hL : M.IsLowerTriangular) (h1 : ∀ i, M i i = 1) (x : Fin n → K) (i : Fin n) :
    (M *ᵥ x) i = x i + ∑ j ∈ Finset.Iio i, M i j * x j := by
  classical
  change ∑ j, M i j * x j = _
  rw [← Finset.sum_subset (Finset.subset_univ (insert i (Finset.Iio i))) (fun j _ hj => ?_),
    Finset.sum_insert (by simp), h1, one_mul]
  have hij : i < j := by simpa [not_or, lt_iff_le_and_ne] using hj
  rw [hL hij, zero_mul]

/-- Rational entries are encoded at a common radix by signed numerator and
unit denominator. No price is charged to any instruction in this query
program. Every address field outside the selected slots is preserved. -/
theorem compile_endpointMatrix {J : Type} [DecidableEq J] {p : ℕ}
    (rank : J → ℕ) (slot : Fin (c + (b+e)) → Spot J)
    (hs : Function.Injective slot) (order : ∀ i j, i < j → Lag.early rank (slot i) (slot j))
    (G : Matrix (Fin b) (Fin c) ℚ) (D : Matrix (Fin e) (Fin b) ℚ)
    (G' : (f : ℕ) → Matrix (Fin b) (Fin c) (Tower p f))
    (D' : (f : ℕ) → Matrix (Fin e) (Fin b) (Tower p f))
    (hG : ∀ f, MatrixToken G (G' f)) (hD : ∀ f, MatrixToken D (D' f))
    (code : ℚ → Pinpoint p)
    (hcode : ∀ i j f, Token (endpointMatrix G D i j) ((code (endpointMatrix G D i j)).stamp f)) :
    ∃ prog : List (Lag J p), (∀ v ∈ prog, v.legal rank ∧ v.prices = 0) ∧
      ∀ f (x : Duplex J (Tower p f)),
        let y := prog.foldl (Lag.fire f) x
        (∀ i, hear y (slot i) =
          (endpointMatrix (G' f) (D' f) *ᵥ (fun j => hear x (slot j))) i) ∧
        (∀ a, (∀ i, a ≠ slot i) → hear y a = hear x a) := by
  obtain ⟨prog, hleg, hv⟩ := NearSquareRoot.InterchangeTriangular.compile slot (fun _ => Span.one)
    (fun i j => code (endpointMatrix G D i j)) rank hs order
  refine ⟨prog, hleg, fun f x => ?_⟩
  refine ⟨fun i => ?_, (hv f x).2⟩
  rw [(hv f x).1 i, triangular_dot _ (endpointMatrix_lower _ _) (endpointMatrix_diagonal _ _)]
  simp only [NearSquareRoot.InterchangeTriangular.rowValue, Span.land_one, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => congrArg (· * hear x (slot j))
    ((hcode i j f).unique (endpointMatrix_token (hG f) (hD f) i j))

private def entrySet {I J : Type*} [Fintype I] [Fintype J] (A : Matrix I J ℚ) : Finset ℚ :=
  Finset.univ.image fun ij : I × J => A ij.1 ij.2

private theorem mem_entrySet {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℚ) (i : I) (j : J) : A i j ∈ entrySet A :=
  Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩

/-- Interpret the entries stored in a finite rational coefficient catalog. -/
def matrixAt {I J : Type*} {p : ℕ} (code : ℚ → Pinpoint p) (f : ℕ) (A : Matrix I J ℚ) :
    Matrix I J (Tower p f) := A.map fun q => (code q).stamp f

/-- One prime suffices for every endpoint in a finite family, every main-pair
query, and every recursive width. Each program acts on the actual two-wing
layout with arbitrary contents in the other main and reserve fields. The
additional finite catalog is available to the other stages of the algorithm. -/
theorem compile_physical_endpoints {T : Type*} [Fintype T] (a m W : ℕ) (c e : T → ℕ)
    (he : ∀ t, c t + e t = a) (G : (t : T) → Matrix (Fin 2) (Fin (c t)) ℚ)
    (D : (t : T) → Matrix (Fin (e t)) (Fin 2) ℚ) (extra : Finset ℚ) :
    ∃ p, p.Prime ∧ W < p ∧ ∃ code : ℚ → Pinpoint p,
      (∀ q ∈ extra, ∀ f, Token q ((code q).stamp f)) ∧
      (∀ t f, MatrixToken (G t) (matrixAt code f (G t)) ∧
        MatrixToken (D t) (matrixAt code f (D t))) ∧
      ∀ (t : T) (j : Fin m),
        let slot := NearSquareRoot.InterchangeSlots.active (he t) j
        ∃ prog : List (Lag (Fin (a+m+a)) p),
          (∀ v ∈ prog, v.legal Fin.val ∧ v.prices = 0) ∧
          ∀ f (x : Duplex (Fin (a+m+a)) (Tower p f)),
            let y := prog.foldl (Lag.fire f) x
            (∀ i, hear y (slot i) =
              (endpointMatrix (matrixAt code f (G t)) (matrixAt code f (D t)) *ᵥ
                (fun k => hear x (slot k))) i) ∧
            (∀ s, (∀ i, s ≠ slot i) → hear y s = hear x s) := by
  classical
  let catalog := fun t => entrySet (G t) ∪ entrySet (D t) ∪ entrySet (endpointMatrix (G t) (D t))
  obtain ⟨p, hp, hW, code, h⟩ :=
    exists_instruction_pinpoints W (extra ∪ Finset.univ.biUnion catalog)
  have localToken (t : T) {q : ℚ} (hq : q ∈ catalog t) :=
    (h q (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hq⟩))).2
  have stored (t : T) (f : ℕ) : MatrixToken (G t) (matrixAt code f (G t)) ∧
      MatrixToken (D t) (matrixAt code f (D t)) := by
    constructor <;> intro i j
    · exact localToken t (Finset.mem_union_left _ (Finset.mem_union_left _ (mem_entrySet _ i j))) f
    · exact localToken t (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_entrySet _ i j))) f
  refine ⟨p, hp, hW, code, fun q hq => (h q (Finset.mem_union_left _ hq)).2, stored, fun t j => ?_⟩
  exact compile_endpointMatrix Fin.val _ (NearSquareRoot.InterchangeSlots.active_injective (he t) j)
    (NearSquareRoot.InterchangeSlots.active_order (he t) j) _ _ _ _
    (fun f => (stored t f).1) (fun f => (stored t f).2) code fun i k =>
      localToken t (Finset.mem_union_right _ (mem_entrySet _ i k))

end Interchange

end NearSquareRoot
end Computability
end OAI
