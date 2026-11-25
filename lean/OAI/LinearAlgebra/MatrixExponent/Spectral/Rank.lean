import OAI.LinearAlgebra.MatrixExponent.Spectral.Semiring
import Mathlib.Logic.Equiv.Prod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.LinearAlgebra.MatrixExponent.Prices.Padding

/-!
# Adding trivial sites and closing them with local covectors
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S : Type} [Field K] [Fintype S] (U : Type) [Fintype U]

/-- The new sites have one trivial coordinate. -/
def pad (A : Raw K S) : Raw K (S ⊕ U) where
  leg := Sum.elim A.leg fun _ => Unit
  fleg := Sum.rec (fun s => A.fleg s) (fun _ => inferInstanceAs (Fintype Unit))
  term := A.term
  factor i := Sum.rec (A.factor i) fun _ _ => 1

variable {U} [Nonempty S]

abbrev Covectors (A : Raw K (S ⊕ U)) := ∀ u, A.leg (.inr u) → K

/-- Scalar from closing the extra sites, evaluated separately on each term. -/
def scalar (A : Raw K (S ⊕ U)) (v : A.Covectors) (i : A.term) : K :=
  ∏ u, ∑ y, v u y * A.factor i (.inr u) y

open Classical in
def weight (a : K) (s : S) : K := if s = Classical.arbitrary S then a else 1

/-- Closing a term multiplies one of its remaining factors by the scalar. -/
def close (A : Raw K (S ⊕ U)) (v : A.Covectors) : Raw K S where
  leg s := A.leg (.inl s)
  term := A.term
  factor i s x := A.factor i (.inl s) x * weight (A.scalar v i) s

omit [Nonempty S] in
theorem pad_coeff (A : Raw K S) (x : ∀ s, (pad U A).leg s) :
    (pad U A).coeff x = A.coeff (fun s => x (.inl s)) := by
  simp only [coeff, Fintype.prod_sum_type]
  change (∑ i : A.term, (∏ s, A.factor i s (x (.inl s))) * ∏ _ : U, (1 : K)) = _
  simp

theorem close_action (A : Raw K (S ⊕ U)) (v : A.Covectors)
    (w : ∀ s, A.leg (.inl s) → K) :
    (∑ i : (A.close v).term, ∏ s, ∑ y, w s y * (A.close v).factor i s y) =
      ∑ i : A.term, (∏ s, ∑ y, w s y * A.factor i (.inl s) y) * A.scalar v i := by
  classical
  change (∑ i : A.term, ∏ s, ∑ y, w s y * (A.factor i (.inl s) y * weight (A.scalar v i) s)) = _
  simp only [← mul_assoc, ← Finset.sum_mul, Finset.prod_mul_distrib]
  simp [weight]

/-- A restriction to a padded tensor uses one covector per extra site. -/
theorem restricts_pad_iff (A : Raw K (S ⊕ U)) (B : Raw K S) :
    A.Restricts (pad U B) ↔ ∃ v : A.Covectors, (A.close v).Restricts B := by
  constructor
  · rintro ⟨L, h⟩
    let v : A.Covectors := fun u => L (.inr u) ()
    refine ⟨v, fun s => L (.inl s), fun x => ?_⟩
    let x' : ∀ s, (pad U B).leg s := Sum.rec x (fun _ => ())
    refine Eq.trans ?_ (close_action A v (fun s => L (.inl s) (x s))).symm
    have hx := h x'
    rw [pad_coeff] at hx
    simp only [Fintype.prod_sum_type] at hx
    exact hx
  · rintro ⟨v, L, h⟩
    refine ⟨Sum.rec L (fun u _ => v u), fun x => ?_⟩
    refine (pad_coeff B x).trans ((h _).trans ((close_action A v
      (fun s => L s (x (.inl s)))).trans ?_))
    simp only [Fintype.prod_sum_type]
    rfl

omit [Fintype S] [Nonempty S] in
theorem pad_scalar (A : Raw K S) (v : (pad U A).Covectors) (i : A.term) :
    (pad U A).scalar v i = ∏ u, v u () := by
  change U → Unit → K at v
  change (∏ u, ∑ y : Unit, v u y * 1) = _
  simp

theorem pad_restricts_iff (A B : Raw K S) :
    (pad U A).Restricts (pad U B) ↔ A.Restricts B := by
  classical
  rw [restricts_pad_iff]
  constructor
  · rintro ⟨v, h⟩
    suffices A.Restricts ((pad U A).close v) from this.trans h
    refine ⟨fun s x y => if y = x then weight (∏ u, v u ()) s else 0, fun x => ?_⟩
    change (∀ s, A.leg s) at x
    change (∑ i : A.term, ∏ s, A.factor i s (x s) * weight ((pad U A).scalar v i) s) = _
    simp [pad_scalar, mul_comm]
  · intro h
    let v : (pad U A).Covectors := fun _ _ => 1
    have he : ((pad U A).close v) ≈ A := by
      refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i s x => ?_
      change A.term at i
      change A.factor i s x * weight ((pad U A).scalar v i) s = A.factor i s x
      simp [pad_scalar, weight, v]
    exact ⟨v, he.1.trans h⟩

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

/-!
# Adjoining unit legs

Padding preserves zero, one and products up to mutual restriction.
For sums, one can erase the summand label at every new site.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S : Type} [Field K] [Fintype S] (U : Type) [Fintype U]

theorem pad_zero : pad U (0 : Raw K S) ≈ 0 := by
  constructor <;>
    exact ⟨fun _ _ _ => 0, fun _ => Finset.sum_congr rfl fun i _ => Empty.elim i⟩

theorem pad_one : pad U (1 : Raw K S) ≈ 1 := by
  let e (s : S ⊕ U) : (pad U (1 : Raw K S)).leg s ≃ Unit :=
    match s with
    | .inl _ => Equiv.refl Unit
    | .inr _ => Equiv.refl Unit
  refine relabel (Equiv.refl _) e ?_
  rintro i (s | u) x <;> rfl

theorem pad_mul (A B : Raw K S) : pad U (A * B) ≈ pad U A * pad U B := by
  let e (s : S ⊕ U) : (pad U (A * B)).leg s ≃ (pad U A * pad U B).leg s :=
    match s with
    | .inl s => Equiv.refl (A.leg s × B.leg s)
    | .inr _ => (Equiv.punitProd Unit).symm
  refine relabel (Equiv.refl _) e ?_
  rintro i (s | u) x
  · rfl
  · exact (one_mul (1 : K)).symm

theorem pad_add (A B : Raw K S) : (pad U A + pad U B).Restricts (pad U (A + B)) := by
  classical
  let L (s : S ⊕ U) : (pad U (A + B)).leg s → (pad U A + pad U B).leg s → K :=
    match s with
    | .inl s => fun (x y : A.leg s ⊕ B.leg s) => if y = x then 1 else 0
    | .inr _ => fun _ _ => 1
  refine ⟨L, fun x => Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun s _ => ?_⟩
  change A.term ⊕ B.term at i
  cases s with
  | inl s =>
    have key (z : A.leg s ⊕ B.leg s) (f : A.leg s ⊕ B.leg s → K) :
        f z = ∑ y, (if y = z then (1 : K) else 0) * f y := by simp [ite_mul]
    exact key (x (.inl s)) ((A + B).factor i s)
  | inr u =>
    change 1 = ∑ y : Unit ⊕ Unit, 1 * (pad U A + pad U B).factor i (.inr u) y
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, one_mul]
    cases i
    · exact (add_zero (1 : K)).symm
    · exact (zero_add (1 : K)).symm

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

/-!
# Arrays and diagonal tensors
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable (K S : Type) [Field K] [Fintype S]

/-- One copy of the scalar unit for each possible value of a common label. -/
def diag (X : Type) [Fintype X] [DecidableEq X] : Raw K S :=
  ⟨fun _ => X, X, fun i _ x => if x = i then 1 else 0⟩

variable {K S}

theorem Restricts.zero (A : Raw K S) [Nonempty S] : A.Restricts 0 :=
  ⟨fun _ x _ => Empty.elim x, fun x => Empty.elim (x (Classical.arbitrary S))⟩

theorem zero_restricts_iff (A : Raw K S) :
    (0 : Raw K S).Restricts A ↔ ∀ x, A.coeff x = 0 := by
  constructor
  · rintro ⟨L, h⟩ x
    rw [h]
    exact Finset.sum_eq_zero (fun i _ => Empty.elim i)
  · intro h
    refine ⟨fun _ _ _ => 0, fun x => ?_⟩
    rw [h]
    exact (Finset.sum_eq_zero (fun i _ => Empty.elim i)).symm

theorem diag_equiv {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) : diag K S X ≈ diag K S Y := by
  refine relabel e (fun _ => e) fun i _ x => ?_
  change X at x i
  change (if x = i then (1 : K) else 0) = if e x = e i then 1 else 0
  simp only [e.apply_eq_iff_eq]

theorem diag_sum (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    diag K S (X ⊕ Y) ≈ diag K S X + diag K S Y := by
  refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_
  intro i s x
  change X ⊕ Y at x i
  change (if x = i then (1 : K) else 0) = _
  rcases i with i | i <;> rcases x with x | x <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte] <;> rfl

theorem term_bound (A : Raw K S) [DecidableEq A.term] :
    (diag K S A.term).Restricts A := by
  refine ⟨fun s x i => A.factor i s x, fun x => ?_⟩
  change A.coeff x = ∑ i : A.term, ∏ s, ∑ j : A.term,
    A.factor j s (x s) * if j = i then 1 else 0
  simp [coeff, mul_ite]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

/-!
# A diagonal restriction cannot increase the number of labels

Assign one label to a single site and a second label to all remaining
sites. This slice of the target diagonal is the identity matrix. The
restriction factors the slice through the source label space.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S : Type} [Field K] [Fintype S] [Nontrivial S]

theorem diag_restricts_le {m n : ℕ}
    (h : (diag K S (Fin n)).Restricts (diag K S (Fin m))) : m ≤ n := by
  classical
  obtain ⟨u, v, huv⟩ := exists_pair_ne S
  obtain ⟨L, hL⟩ := h
  change S → Fin m → Fin n → K at L
  change ∀ x : S → Fin m, (∑ i : Fin m, ∏ s, if x s = i then (1 : K) else 0) =
    ∑ i : Fin n, ∏ s, ∑ y : Fin n, L s (x s) y * if y = i then 1 else 0 at hL
  simp [mul_ite] at hL
  let A : Matrix (Fin m) (Fin n) K := L u
  let B : Matrix (Fin n) (Fin m) K := fun k j => ∏ s ∈ Finset.univ.erase u, L s j k
  have hAB : A * B = 1 := by
    ext i j
    let x : S → Fin m := fun s => if s = u then i else j
    rw [Matrix.mul_apply, Matrix.one_apply]
    calc
      _ = ∑ k : Fin n, ∏ s, L s (x s) k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u)]
        simp only [A, B, x, ↓reduceIte]
        congr 1
        apply Finset.prod_congr rfl
        intro s hs
        rw [ite_eq_right (Finset.ne_of_mem_erase hs)]
      _ = ∑ k : Fin m, ∏ s, if x s = k then (1 : K) else 0 := (hL x).symm
      _ = _ := by
        rw [Finset.sum_eq_single i]
        · by_cases hij : i = j
          · simp [x, hij]
          · rw [ite_eq_right hij]
            exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [x, huv.symm, Ne.symm hij])
        · intro k _ hk
          exact Finset.prod_eq_zero (Finset.mem_univ u) (by simp [x, Ne.symm hk])
        · simp
  have hr := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  simpa [hAB] using hr

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

section
/-!
# Closing sums and products

On a direct sum the covector is restricted to each summand. In a
product with a padded tensor only the other tensor is contracted.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S U : Type} [Field K] [Fintype S] [Fintype U] [Nonempty S]

theorem close_add (A B : Raw K (S ⊕ U)) (v : (A + B).Covectors) :
    (A + B).close v ≈ A.close (fun u x => v u (.inl x)) + B.close (fun u x => v u (.inr x)) := by
  have hl (i : A.term) :
      (A + B).scalar v (.inl i) = A.scalar (fun u x => v u (.inl x)) i := by
    apply Finset.prod_congr rfl
    intro u _
    change (∑ y : A.leg (.inr u) ⊕ B.leg (.inr u),
      v u y * Sum.elim (A.factor i (.inr u)) (fun _ => 0) y) = _
    simp [Fintype.sum_sum_type]
  have hr (i : B.term) :
      (A + B).scalar v (.inr i) = B.scalar (fun u x => v u (.inr x)) i := by
    apply Finset.prod_congr rfl
    intro u _
    change (∑ y : A.leg (.inr u) ⊕ B.leg (.inr u),
      v u y * Sum.elim (fun _ => 0) (B.factor i (.inr u)) y) = _
    simp [Fintype.sum_sum_type]
  refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_
  rintro (i | i) s (x | x)
  · exact congrArg (fun a => A.factor i (.inl s) x * weight a s) (hl i)
  · exact zero_mul _
  · exact zero_mul _
  · exact congrArg (fun a => B.factor i (.inl s) x * weight a s) (hr i)

theorem close_mul (A : Raw K S) (B : Raw K (S ⊕ U)) (v : (pad U A * B).Covectors) :
    (pad U A * B).close v ≈ A * B.close (fun u x => v u ((), x)) := by
  refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_
  rintro ⟨i, j⟩ s ⟨x, y⟩
  have h : (pad U A * B).scalar v (i, j) = B.scalar (fun u z => v u ((), z)) j := by
    apply Finset.prod_congr rfl
    intro u _
    change (∑ z : Unit × B.leg (.inr u), v u z * (1 * B.factor j (.inr u) z.2)) = _
    simp [Fintype.sum_prod_type]
    rfl
  change A.factor i s x * B.factor j (.inl s) y * weight ((pad U A * B).scalar v (i, j)) s = _
  rw [h, mul_assoc]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

/-!
# Natural units and rank bounds

A decomposition with `n` terms is a restriction from the `n`-fold diagonal.
Reflection of the natural order requires at least two sites.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S : Type} [Field K] [Fintype S]

theorem diag_fin (n : ℕ) : ofRaw (Raw.diag K S (Fin n)) = n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact ofRaw_eq (Raw.relabel (Equiv.equivOfIsEmpty (Fin 0) Empty)
      (fun _ => Equiv.equivOfIsEmpty (Fin 0) Empty) (fun i => Fin.elim0 i))
  | succ n ih =>
    have h : ofRaw (Raw.diag K S (Fin 1)) = (1 : Tensor K S) := by
      apply ofRaw_eq
      refine Raw.relabel (Equiv.ofUnique (Fin 1) Unit)
        (fun _ => Equiv.ofUnique (Fin 1) Unit) fun i s x => ?_
      change Fin 1 at x i
      change (if x = i then (1 : K) else 0) = 1
      rw [ite_eq_left (Subsingleton.elim _ _)]
    rw [ofRaw_eq (Raw.diag_equiv finSumFinEquiv.symm), ofRaw_eq (Raw.diag_sum _ _),
      ofRaw_add, ih, h, Nat.cast_succ]

theorem diag_eq_natCast (X : Type) [Fintype X] [DecidableEq X] :
    ofRaw (Raw.diag K S X) = Fintype.card X := by
  rw [ofRaw_eq (Raw.diag_equiv (Fintype.equivFin X)), diag_fin]

theorem le_term_count (A : Raw K S) : ofRaw A ≤ Fintype.card A.term := by
  classical
  rw [← diag_eq_natCast, ofRaw_le]
  exact Raw.term_bound A

theorem exists_bound (A : Tensor K S) : ∃ n : ℕ, A ≤ n :=
  Quotient.inductionOn A fun a => ⟨_, le_term_count a⟩

variable [Nonempty S]

theorem zero_le (A : Tensor K S) : 0 ≤ A :=
  Quotient.inductionOn A fun a => Raw.Restricts.zero a

theorem ofRaw_eq_zero (A : Raw K S) : ofRaw A = 0 ↔ ∀ x, A.coeff x = 0 := by
  rw [← Raw.zero_restricts_iff, ← ofRaw_le]
  exact ⟨le_of_eq, fun h => le_antisymm h (zero_le _)⟩

theorem one_le (A : Tensor K S) : A ≠ 0 → 1 ≤ A := by
  refine Quotient.inductionOn A fun a ha => Raw.restricts_one a ?_
  exact not_forall.mp (fun h => ha ((ofRaw_eq_zero _).mpr h))

instance : Nontrivial (Tensor K S) := by
  refine ⟨1, 0, fun h => ?_⟩
  have he := (ofRaw_eq_zero (1 : Raw K S)).mp h (fun _ => ())
  change (∑ _ : Unit, ∏ _ : S, (1 : K)) = 0 at he
  simp at he

theorem natCast_le {m n : ℕ} (h : m ≤ n) : (m : Tensor K S) ≤ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa [Nat.cast_add, add_comm] using
    add_le_add_right 0 (d : Tensor K S) m (zero_le _)

theorem natCast_le_iff [Nontrivial S] (m n : ℕ) : (m : Tensor K S) ≤ n ↔ m ≤ n := by
  refine ⟨?_, natCast_le⟩
  rw [← diag_fin, ← diag_fin, ofRaw_le]
  exact Raw.diag_restricts_le

/-- The coordinate expansion bounds rank by the product of the leg dimensions. -/
theorem le_dimension (A : Raw K S) : ofRaw A ≤ (∏ s, Fintype.card (A.leg s) : ℕ) := by
  classical
  let B := Raw.ofTable A.leg A.coeff
  have he : A ≈ B := Raw.equiv_coeff (fun _ => Equiv.refl _) fun x =>
    (Raw.coeff_ofTable _ _ x).symm
  rw [ofRaw_eq he, ← Fintype.card_pi]
  exact le_term_count B

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Orders after adjoining trivial tensor legs
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S : Type} [Field K] [Fintype S] [Nonempty S] (U : Type) [Fintype U]

def pad : Tensor K S → Tensor K (S ⊕ U) :=
  Quotient.map (Raw.pad U) fun _ _ h =>
    ⟨(Raw.pad_restricts_iff _ _).mpr h.1, (Raw.pad_restricts_iff _ _).mpr h.2⟩

theorem pad_ofRaw (A : Raw K S) : pad U (ofRaw A) = ofRaw (Raw.pad U A) := rfl

theorem pad_le_ofRaw_iff {U : Type} [Fintype U] (s : Tensor K S) (A : Raw K (S ⊕ U)) :
    pad U s ≤ ofRaw A ↔ ∃ v : A.Covectors, s ≤ ofRaw (A.close v) :=
  Quotient.inductionOn s fun a => Raw.restricts_pad_iff A a

theorem pad_close_le (A : Raw K (S ⊕ U)) (v : A.Covectors) :
    pad U (ofRaw (A.close v)) ≤ ofRaw A :=
  (pad_le_ofRaw_iff _ A).mpr ⟨v, le_rfl⟩

theorem padding : Prices.Padding (pad (K := K) (S := S) U) where
  zero := ofRaw_eq (Raw.pad_zero U)
  one := ofRaw_eq (Raw.pad_one U)
  le_iff s t := Quotient.inductionOn₂ s t fun a b => Raw.pad_restricts_iff b a
  mul s t := Quotient.inductionOn₂ s t fun a b => ofRaw_eq (Raw.pad_mul U a b)
  add_le s t := Quotient.inductionOn₂ s t fun a b => Raw.pad_add U a b
  split {s x y} := by
    refine Quotient.inductionOn₂ x y fun A B h => ?_
    obtain ⟨v, hv⟩ := (pad_le_ofRaw_iff s (A + B)).mp h
    rw [ofRaw_eq (Raw.close_add _ _ v), ofRaw_add] at hv
    exact ⟨_, _, pad_close_le U A _, pad_close_le U B _, hv⟩
  factor {s a x} := by
    refine Quotient.inductionOn₂ a x fun A B h => ?_
    obtain ⟨v, hv⟩ := (pad_le_ofRaw_iff s (Raw.pad U A * B)).mp h
    rw [ofRaw_eq (Raw.close_mul _ _ v), ofRaw_mul] at hv
    exact ⟨_, pad_close_le U B _, hv⟩

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end
