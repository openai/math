import OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw
import OAI.LinearAlgebra.SpectralBooks.WireTransport

/-! # Local restrictions for the two exterior factorizations

The background indices carry arbitrary coefficients and arbitrary placements.
The three additional indices of a child are the fresh mark, exterior column,
and exterior row in that order.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical BigOperators

namespace SiteTensor.Relocation

variable {I J Q H M : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [∀ i, Fintype (A i)]
variable [Fintype Q] [Fintype H] [Fintype M] [CommSemiring K]

/-- A coefficient array with one distinguished factor. -/
def marked (A : I → Type) [∀ i, Fintype (A i)] (Q : Type) [Fintype Q]
    (T : (∀ i, A i) → Q → K) : Raw (I ⊕ Unit) K where
  Leg := Sum.elim A (fun _ => Q)
  finiteLeg := fun k => by
    rcases k with i | _
    · exact inferInstanceAs (Fintype (A i))
    · exact inferInstanceAs (Fintype Q)
  coeff x := T (fun i => x (.inl i)) (x (.inr ()))

/-- A split coefficient array with independent mark, column, and row factors. -/
def split (A : I → Type) [∀ i, Fintype (A i)] (Q H : Type) [Fintype Q] [Fintype H]
    (S : (∀ i, A i) → Q → H → H → K) : Raw (I ⊕ Fin 3) K where
  Leg := Sum.elim A ![Q,H,H]
  finiteLeg := fun k => by
    rcases k with i | t
    · exact inferInstanceAs (Fintype (A i))
    · change Fintype (![Q,H,H] t)
      exact Fin.cases (motive := fun k => Fintype (![Q,H,H] k)) (inferInstanceAs (Fintype Q))
        (fun t => Fin.cases (motive := fun k => Fintype (![H,H] k)) (inferInstanceAs (Fintype H))
          (fun t => Fin.cases (motive := fun k => Fintype (![H] k)) (inferInstanceAs (Fintype H))
            (fun t => t.elim0) t) t) t
  coeff x := S (fun i => x (.inl i)) (x (.inr 0)) (x (.inr 1)) (x (.inr 2))

/-- Place just the marked factor, preserving all background sites. -/
def placeMark (σ : I → J) (p : J) : I ⊕ Unit → J := Sum.elim σ (fun _ => p)

/-- Place the marked factor and its exterior column and row. -/
def placeSplit (σ : I → J) (c a b : J) : I ⊕ Fin 3 → J := Sum.elim σ ![c,a,b]

/-- The first exterior factorization, in operator order DL. -/
def plusCoeff (T : (∀ i, A i) → Q → K) (L : Q → M → H → K) (D : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) : K :=
  ∑ j, ∑ m, T x j * L i m α * D j β m

/-- The second exterior factorization, in operator order LD. -/
def minusCoeff (T : (∀ i, A i) → Q → K) (D : Q → M → H → K) (L : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) : K :=
  ∑ j, ∑ m, T x j * D j m α * L i β m

/-- The wire supplying the common intermediate label for a local contraction. -/
def wire (K : Type*) (M : Type) [CommSemiring K] [Fintype M] (p q : J) : Raw J K :=
  (Raw.diagonal (Fin 2) K M).group ![p,q]

private def markTupleEquiv (A : I → Type) (Q : Type) :
    ((∀ i, A i) × Q) ≃ (∀ k : I ⊕ Unit, Sum.elim A (fun _ => Q) k) where
  toFun w k := match k with
    | .inl i => w.1 i
    | .inr _ => w.2
  invFun x := (fun i => x (.inl i), x (.inr ()))
  left_inv _ := rfl
  right_inv x := by funext k; rcases k with i | ⟨⟩ <;> rfl

/-- Two local matrices sharing a wire index, while all background indices are
copied at their own sites. This also permits the two matrices to act together. -/
theorem restricts_contraction (T : (∀ i, A i) → Q → K) (σ : I → J)
    (p q : J) (S : Raw J K) (readBg : ∀ i, S.Leg (σ i) → A i)
    (P : S.Leg p → M → K) (R : S.Leg q → Q → M → K)
    (hs : ∀ x, S.coeff x = ∑ j, ∑ m, T (fun i => readBg i (x (σ i))) j *
        P (x p) m * R (x q) j m) :
    S.Restricts (((marked A Q T).group (placeMark σ q)).mul (wire K M p q)) := by
  classical
  let U := (marked A Q T).group (placeMark σ q)
  let W := wire K M p q
  let V := U.mul W
  let E : (((∀ i, A i) × Q) × (Fin 2 → M)) ≃ (∀ k, V.Leg k) :=
    ((markTupleEquiv A Q).trans (groupIndexEquiv (placeMark σ q) (marked A Q T).Leg)).prodCongr
      (groupIndexEquiv ![p,q] (fun _ => M)) |>.trans
      (Equiv.arrowProdEquivProdArrow J U.Leg W.Leg).symm
  let ok (k : J) (x : S.Leg k) (y : V.Leg k) :=
    ∀ (i : I) (h : σ i = k), y.1 ⟨.inl i, h⟩ = readBg i (h ▸ x)
  let F (k : J) (x : S.Leg k) (y : V.Leg k) : K :=
    (if ok k x y then 1 else 0) *
      (if hp : p = k then P (hp ▸ x) (y.2 ⟨0,hp⟩) else 1) *
      (if hq : q = k then R (hq ▸ x) (y.1 ⟨.inr (),hq⟩) (y.2 ⟨1,hq⟩) else 1)
  refine ⟨F, fun x => ?_⟩
  rw [← E.sum_comp]
  let b (i : I) := readBg i (x (σ i))
  have term (s : ((∀ i, A i) × Q) × (Fin 2 → M)) :
      V.coeff (E s) * ∏ k, F k (x k) (E s k) =
        ∑ m : M, if s.1.1 = b ∧ s.2 = fun _ => m then
          T b s.1.2 * P (x p) m * R (x q) s.1.2 m else 0 := by
    have hok : (∀ k, ok k (x k) (E s k)) ↔ s.1.1 = b := by
      constructor
      · intro h
        exact funext fun i => h (σ i) i rfl
      · intro h k i hi
        subst k
        exact congrFun h i
    have hp : (∏ k, if hp : p = k then
        P (hp ▸ x k) ((E s k).2 ⟨0,hp⟩) else 1) = P (x p) (s.2 0) := by
      rw [Finset.prod_eq_single p]
      · simp only; rfl
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    have hq : (∏ k, if hq : q = k then
        R (hq ▸ x k) ((E s k).1 ⟨.inr (),hq⟩) ((E s k).2 ⟨1,hq⟩) else 1) =
        R (x q) s.1.2 (s.2 1) := by
      rw [Finset.prod_eq_single q]
      · simp only; rfl
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    have hcoeff : V.coeff (E s) = T s.1.1 s.1.2 * (∑ m : M, if s.2 = fun _ => m then 1 else 0) := by
      change _ * _ = _ * _
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      congr 1
    rw [hcoeff]
    change (T s.1.1 s.1.2 * (∑ m : M, if s.2 = fun _ => m then 1 else 0)) * _ = _
    have hbprod : (∏ k, if ok k (x k) (E s k) then (1 : K) else 0) =
        if s.1.1 = b then 1 else 0 := Fintype.prod_boole.trans (if_congr hok rfl rfl)
    simp only [F, Finset.prod_mul_distrib, hbprod, hp, hq]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hb : s.1.1 = b <;> by_cases hm : s.2 = fun _ => m <;>
      simp [hb, hm, mul_assoc]
  change S.coeff x = ∑ s, V.coeff (E s) * ∏ k, F k (x k) (E s k)
  simp_rw [term]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [hs]
  symm
  rw [Finset.sum_eq_single b]
  · simp [Finset.sum_comm (f := fun (z : Fin 2 → M) (m : M) => _), b]
  · intro a _ ha; simp [ha]
  · simp

/-- For DL the fresh mark and column meet at the first end, while the old
mark and row meet at the second end of the intermediate wire. -/
theorem plus_restricts_opposite (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (c b : J) :
    ((split A Q H (plusCoeff T L D)).group (placeSplit σ c c b)).Restricts
      (((marked A Q T).group (placeMark σ b)).mul (wire K M c b)) :=
  restricts_contraction T σ c b _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => L (x ⟨.inr 0,rfl⟩) m (x ⟨.inr 1,rfl⟩))
    (fun x j m => D j (x ⟨.inr 2,rfl⟩) m) (fun _ => rfl)

/-- For LD the fresh mark and row meet at the first end, and the old mark
and column meet at the second. -/
theorem minus_restricts_opposite (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (c a : J) :
    ((split A Q H (minusCoeff T D L)).group (placeSplit σ c a c)).Restricts
      (((marked A Q T).group (placeMark σ a)).mul (wire K M c a)) := by
  refine restricts_contraction T σ c a _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => L (x ⟨.inr 0,rfl⟩) (x ⟨.inr 2,rfl⟩) m)
    (fun x j m => D j m (x ⟨.inr 1,rfl⟩)) ?_
  intro x
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro m _
  exact mul_right_comm _ _ _

/-- Supplying the exterior column from an arbitrary third site. -/
theorem plus_restricts (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (c a b : J) :
    ((split A Q H (plusCoeff T L D)).group (placeSplit σ c a b)).Restricts
      ((((marked A Q T).group (placeMark σ b)).mul (wire K M c b)).mul (wire K H c a)) := by
  let S := split A Q H (plusCoeff T L D)
  have h := Raw.move_restricts_with_wire S (placeSplit σ c c b) (placeSplit σ c a b)
    (.inr 1) (by
      intro t ht
      rcases t with i | t
      · rfl
      · fin_cases t <;> first | rfl | exact (ht rfl).elim)
  exact restrict_trans h (Raw.mul_restricts (plus_restricts_opposite T L D σ c b) (restrict_refl _))

/-- Supplying the exterior row from an arbitrary third site. -/
theorem minus_restricts (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (c a b : J) :
    ((split A Q H (minusCoeff T D L)).group (placeSplit σ c a b)).Restricts
      ((((marked A Q T).group (placeMark σ a)).mul (wire K M c a)).mul (wire K H c b)) := by
  let S := split A Q H (minusCoeff T D L)
  have h := Raw.move_restricts_with_wire S (placeSplit σ c a c) (placeSplit σ c a b)
    (.inr 2) (by
      intro t ht
      rcases t with i | t
      · rfl
      · fin_cases t <;> first | rfl | exact (ht rfl).elim)
  exact restrict_trans h (Raw.mul_restricts (minus_restricts_opposite T D L σ c a) (restrict_refl _))

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
