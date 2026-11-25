import OAI.LinearAlgebra.MatrixExponent.Spectral.Semiring
import OAI.LinearAlgebra.MatrixExponent.Valued.Restriction
import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank
import OAI.LinearAlgebra.MatrixExponent.Spectral.Wire

/-!
# Grouping local coordinates by a map of sites

The grouped substitutions preserve membership in any fixed subring.
The ordinary restriction statements specialize to the full field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S T : Type} [Field K] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

abbrev Fiber (f : T → S) (s : S) := {t // f t = s}

def group (f : T → S) (A : Raw K T) : Raw K S where
  term := A.term
  leg s := ∀ t : Fiber f s, A.leg t
  factor i s x := ∏ t : Fiber f s, A.factor i t (x t)

omit [DecidableEq T] in
private theorem fiber_prod (f : T → S) (v : ∀ s, Fiber f s → K) :
    (∏ s, ∏ t, v s t) = ∏ t, v (f t) ⟨t, rfl⟩ := by
  rw [← Fintype.prod_fiberwise f (fun t => v (f t) ⟨t, rfl⟩)]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun t _ => ?_
  rcases t with ⟨t, rfl⟩
  rfl

theorem coeff_group (f : T → S) (A : Raw K T) (x : ∀ s, (A.group f).leg s) :
    (A.group f).coeff x = A.coeff (fun t => x (f t) ⟨t, rfl⟩) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact fiber_prod f (fun s t => A.factor i t (x s t))

theorem _root_.OAI.LinearAlgebra.MatrixExponent.Valued.Restricts.group {O : Subring K} {A B : Raw K T}
    (h : Valued.Restricts O A B) (f : T → S) :
    Valued.Restricts O (A.group f) (B.group f) := by
  obtain ⟨L, hL, h⟩ := h
  let M (s : S) (x : (B.group f).leg s) (y : (A.group f).leg s) :=
    ∏ t : Fiber f s, L t (x t) (y t)
  refine ⟨M, fun _ _ _ => O.prod_mem fun t _ => hL t _ _, fun x => ?_⟩
  have hw (i : A.term) (s : S) :
      (∑ y, M s (x s) y * (A.group f).factor i s y) =
        ∏ t : Fiber f s, ∑ y, L t (x s t) y * A.factor i t y := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact Finset.prod_mul_distrib.symm
  rw [coeff_group, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (fiber_prod f (fun s t => ∑ y, L t (x s t) y * A.factor i t y)).symm.trans
    (Finset.prod_congr rfl fun s _ => (hw i s).symm)

theorem Restricts.group {A B : Raw K T} (h : A.Restricts B) (f : T → S) :
    (A.group f).Restricts (B.group f) :=
  ((Valued.top_restricts h).group f).forget

omit [DecidableEq S] in
/-- A local coordinate may be copied from the source or set to zero. -/
theorem _root_.OAI.LinearAlgebra.MatrixExponent.Valued.Restricts.rows {O : Subring K} {A B : Raw K S} (e : B.term ≃ A.term)
    (h : ∀ s x, (∃ y, ∀ i, B.factor i s x = A.factor (e i) s y) ∨
      (∀ i, B.factor i s x = 0)) : Valued.Restricts O A B := by
  classical
  have each s x : ∃ v : A.leg s → K, (∀ y, v y ∈ O) ∧
      ∀ i, B.factor i s x = ∑ y, v y * A.factor (e i) s y := by
    rcases h s x with ⟨y, hy⟩ | hz
    · exact ⟨fun z => if z = y then 1 else 0, fun z => by by_cases e : z = y <;> simp [e],
        fun i => by simp [hy, ite_mul]⟩
    · exact ⟨fun _ => 0, fun _ => O.zero_mem, fun i => by simp [hz]⟩
  choose v hi hv using each
  refine ⟨v, hi, fun x => ?_⟩
  rw [← e.sum_comp]
  simp only [coeff, hv]

omit [DecidableEq S] in
theorem Restricts.rows {A B : Raw K S} (e : B.term ≃ A.term)
    (h : ∀ s x, (∃ y, ∀ i, B.factor i s x = A.factor (e i) s y) ∨
      (∀ i, B.factor i s x = 0)) : A.Restricts B :=
  (Valued.Restricts.rows (O := ⊤) e h).forget

theorem integral_group_zero {O : Subring K} (f : T → S) :
    (Valued.equiv O).r ((0 : Raw K T).group f) 0 :=
  ⟨.rows (Equiv.refl _) fun _ _ => Or.inr (fun i => Empty.elim i),
    .rows (Equiv.refl _) fun _ _ => Or.inr (fun i => Empty.elim i)⟩

theorem group_zero (f : T → S) : (0 : Raw K T).group f ≈ 0 :=
  Valued.forget_equiv (integral_group_zero (O := ⊤) f)

theorem integral_group_one {O : Subring K} (f : T → S) :
    (Valued.equiv O).r ((1 : Raw K T).group f) 1 := by
  refine Valued.relabel (Equiv.refl _) (fun s => Equiv.ofUnique (Fiber f s → Unit) Unit) ?_
  exact fun i s x => Finset.prod_const_one

theorem group_one (f : T → S) : (1 : Raw K T).group f ≈ 1 :=
  Valued.forget_equiv (integral_group_one (O := ⊤) f)

theorem integral_group_mul {O : Subring K} (f : T → S) (A B : Raw K T) :
    (Valued.equiv O).r ((A * B).group f) (A.group f * B.group f) := by
  let g (s : S) : ((A * B).group f).leg s ≃ (A.group f * B.group f).leg s :=
    { toFun := fun x => (fun t => (x t).1, fun t => (x t).2)
      invFun := fun x t => (x.1 t, x.2 t)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Valued.relabel (Equiv.refl _) g fun _ _ _ => Finset.prod_mul_distrib

theorem group_mul (f : T → S) (A B : Raw K T) :
    (A * B).group f ≈ A.group f * B.group f :=
  Valued.forget_equiv (integral_group_mul (O := ⊤) f A B)

/-- On each nonempty fiber, mixed blocks give zero rows. -/
theorem integral_group_add {O : Subring K} (f : T → S) (hf : Function.Surjective f) (A B : Raw K T) :
    (Valued.equiv O).r ((A + B).group f) (A.group f + B.group f) := by
  classical
  let X := (A + B).group f
  let Y := A.group f + B.group f
  let inc (s : S) : Y.leg s → X.leg s :=
    Sum.elim (fun x t => .inl (x t)) (fun x t => .inr (x t))
  have matchRows (s : S) (x : Y.leg s) (i : Y.term) :
      Y.factor i s x = X.factor i s (inc s x) := by
    obtain ⟨t, ht⟩ := hf s
    rcases i with i | i <;> rcases x with x | x
    · rfl
    · exact (Finset.prod_eq_zero (Finset.mem_univ (⟨t, ht⟩ : Fiber f s)) rfl).symm
    · exact (Finset.prod_eq_zero (Finset.mem_univ (⟨t, ht⟩ : Fiber f s)) rfl).symm
    · rfl
  change (Valued.equiv O).r X Y
  refine ⟨.rows (Equiv.refl _) (fun s x => .inl ⟨inc s x, matchRows s x⟩),
    .rows (Equiv.refl _) fun s x => ?_⟩
  by_cases hz : ∀ i, X.factor i s x = 0
  · exact Or.inr hz
  obtain ⟨i, hi⟩ := not_forall.mp hz
  suffices ∃ y, inc s y = x by
    obtain ⟨y, rfl⟩ := this
    exact Or.inl ⟨y, fun j => (matchRows s y j).symm⟩
  have each (t : Fiber f s) : (A + B).factor i t (x t) ≠ 0 :=
    fun h => hi (Finset.prod_eq_zero (Finset.mem_univ t) h)
  rcases i with i | i
  · have h (t : Fiber f s) : ∃ y, Sum.inl y = x t := by
      have hh := each t
      cases hx : x t with
      | inl y => exact ⟨y, rfl⟩
      | inr y => exact False.elim (hh (by rw [hx]; rfl))
    choose y hy using h
    exact ⟨.inl y, funext hy⟩
  · have h (t : Fiber f s) : ∃ y, Sum.inr y = x t := by
      have hh := each t
      cases hx : x t with
      | inl y => exact False.elim (hh (by rw [hx]; rfl))
      | inr y => exact ⟨y, rfl⟩
    choose y hy using h
    exact ⟨.inr y, funext hy⟩

theorem group_add (f : T → S) (hf : Function.Surjective f) (A B : Raw K T) :
    (A + B).group f ≈ A.group f + B.group f :=
  Valued.forget_equiv (integral_group_add (O := ⊤) f hf A B)

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S T : Type} [Field K] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

def group (f : T → S) (hf : Function.Surjective f) : Tensor K T →+* Tensor K S where
  toFun := Quotient.map (Raw.group f) fun _ _ h => ⟨h.1.group f, h.2.group f⟩
  map_zero' := ofRaw_eq (Raw.group_zero f)
  map_one' := ofRaw_eq (Raw.group_one f)
  map_mul' A B := Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Raw.group_mul f a b)
  map_add' A B := Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Raw.group_add f hf a b)

theorem group_ofRaw (f : T → S) (hf : Function.Surjective f) (A : Raw K T) :
    group f hf (ofRaw A) = ofRaw (A.group f) := rfl

theorem group_mono (f : T → S) (hf : Function.Surjective f) :
    Monotone (group (K := K) f hf) :=
  fun A B => Quotient.inductionOn₂ A B fun _ _ h => Raw.Restricts.group h f

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Averaging quadrilateral inequalities on a binary cube

Apply the square bound at every translate and sum. Each side and each
diagonal then occurs twice. Recurse by halving the flipped coordinate set.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral

abbrev Cube (n : ℕ) := Fin n → Bool

namespace Cube

variable {n : ℕ}

def flip (J : Finset (Fin n)) (x : Cube n) : Cube n :=
  fun i => if i ∈ J then !(x i) else x i

@[simp] theorem flip_flip (J : Finset (Fin n)) (x : Cube n) : flip J (flip J x) = x := by
  funext i
  by_cases h : i ∈ J <;> simp [flip, h]

theorem flip_union {I J : Finset (Fin n)} (h : Disjoint I J) (x : Cube n) :
    flip (I ∪ J) x = flip I (flip J x) := by
  funext i
  by_cases hi : i ∈ I
  · simp [flip, hi, Finset.disjoint_left.mp h hi]
  · simp [flip, hi]

private theorem sum_flip (J : Finset (Fin n)) (f : Cube n → ℝ) :
    ∑ x, f (flip J x) = ∑ x, f x :=
  Equiv.sum_comp (⟨flip J, flip J, flip_flip J, flip_flip J⟩ : Equiv.Perm (Cube n)) f

variable (d : Cube n → Cube n → ℝ) {κ : ℝ}
variable (hs : ∀ a b c e, (d a c) ^ 2 + (d b e) ^ 2 ≤
  κ * ((d a b) ^ 2 + (d b c) ^ 2 + (d c e) ^ 2 + (d e a) ^ 2))

def energy (J : Finset (Fin n)) : ℝ := ∑ x, (d x (flip J x)) ^ 2

include hs in
private theorem energy_split {I J : Finset (Fin n)} (h : Disjoint I J) :
    energy d (I ∪ J) ≤ κ * (energy d I + energy d J) := by
  let f (I : Finset (Fin n)) (x : Cube n) := (d x (flip I x)) ^ 2
  have bound (x : Cube n) :
      f (I ∪ J) x + f (I ∪ J) (flip I x) ≤
        κ * (f I x + f J (flip I x) + f I (flip (I ∪ J) x) + f J (flip J x)) := by
    have hj : flip (I ∪ J) (flip I x) = flip J x := by
      rw [Finset.union_comm, flip_union h.symm, flip_flip]
    have hi : flip I (flip (I ∪ J) x) = flip J x := by rw [flip_union h, flip_flip]
    have hu : flip J (flip I x) = flip (I ∪ J) x := by rw [← flip_union h.symm, Finset.union_comm]
    simp only [f, hj, hi, hu, flip_flip]
    exact hs _ _ _ _
  have H := Finset.sum_le_sum (s := Finset.univ) (fun x _ => bound x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_flip] at H
  change energy d (I ∪ J) + energy d (I ∪ J) ≤
    κ * (energy d I + energy d J + energy d I + energy d J) at H
  linarith

include hs in
theorem energy_bound (hk : 0 ≤ κ) {m : ℝ}
    (he : ∀ x i, (d x (flip {i} x)) ^ 2 ≤ m) (k : ℕ)
    (J : Finset (Fin n)) (hJ : J.card = 2 ^ k) :
    energy d J ≤ (2 * κ) ^ k * Fintype.card (Cube n) * m := by
  induction k generalizing J with
  | zero =>
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hJ
    simpa [energy] using Finset.sum_le_sum (s := Finset.univ) (fun x _ => he x i)
  | succ k ih =>
    rw [pow_succ] at hJ
    obtain ⟨I, hi, hI⟩ := Finset.exists_subset_card_eq (show 2 ^ k ≤ J.card by omega)
    have hr : (J \ I).card = 2 ^ k := by rw [Finset.card_sdiff_of_subset hi]; omega
    calc
      energy d J = energy d (I ∪ (J \ I)) := by rw [Finset.union_sdiff_of_subset hi]
      _ ≤ κ * (energy d I + energy d (J \ I)) := energy_split d hs Finset.disjoint_sdiff
      _ ≤ κ * ((2 * κ) ^ k * Fintype.card (Cube n) * m + (2 * κ) ^ k * Fintype.card (Cube n) * m) :=
        mul_le_mul_of_nonneg_left (add_le_add (ih I hI) (ih _ hr)) hk
      _ = _ := by ring

end Cube
end OAI.LinearAlgebra.MatrixExponent.Spectral
end

/-! # A connected wire graph supplies a common binary label -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable (K : Type) [Field K] {S I : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype I]

theorem connected (A B : I → S)
    (h : ∀ U : Finset S, U.Nonempty → U ≠ Finset.univ → ∃ i, A i ∈ U ∧ B i ∉ U) :
    (2 : Tensor K S) ≤ ∏ i, wire K (A i) (B i) 2 := by
  classical
  let P (U : Finset S) := U.Nonempty ∧ ∃ E : Finset I,
    (∀ i ∈ E, B i ∈ U) ∧ shared K U 2 ≤ ∏ i ∈ E, wire K (A i) (B i) 2
  have hi : ∃ U, P U := by
    let a := Classical.arbitrary S
    refine ⟨{a}, by simp, ∅, by simp, ?_⟩
    rw [show shared K {a} 2 = 1 by simpa [wire] using wire_self K a (n := 2) (by decide), Finset.prod_empty]
    exact le_rfl
  obtain ⟨U, ⟨hne, E, hE, hU⟩, hmax⟩ := Set.Finite.exists_maximal (Set.toFinite {U | P U}) hi
  have hu : U = Finset.univ := by
    by_contra hu
    obtain ⟨i, ha, hb⟩ := h U hne hu
    have fresh : i ∉ E := fun hk => hb (hE i hk)
    have ext : P (insert (B i) U) := by
      refine ⟨by simp, insert i E, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp
        · exact Finset.mem_insert_of_mem (hE _ hj)
      · rw [Finset.prod_insert fresh]
        have step := shared_join K (U := {A i, B i}) (by simp) ha 2
        rw [show ({A i, B i} : Finset S) ∪ U = insert (B i) U by simp [ha]] at step
        exact step.trans (mul_le_mul_left _ _ _ hU)
    exact hb (hmax ext (Finset.subset_insert _ _) (Finset.mem_insert_self _ _))
  rw [hu, shared_all, Nat.cast_ofNat] at hU
  let : MulLeftMono (Tensor K S) := ⟨fun c a b h => mul_le_mul_left a b c h⟩
  exact hU.trans (Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
    (fun _ _ _ => one_le_wire K _ _ (by decide)))

theorem cube_connected (n : ℕ) :
    (2 : Tensor K (Cube n)) ≤ ∏ i : Cube n × Fin n, wire K i.1 (Cube.flip {i.2} i.1) 2 := by
  apply connected
  intro U ⟨x, hx⟩ hU
  by_contra! bad
  have closed (J : Finset (Fin n)) : Cube.flip J x ∈ U := by
    induction J using Finset.induction_on with
    | empty => rw [show Cube.flip ∅ x = x by funext i; simp [Cube.flip]]; exact hx
    | insert i J hi ih =>
      rw [← Finset.singleton_union, Cube.flip_union (by simp [hi])]
      exact bad (Cube.flip J x, i) ih
  apply hU
  apply Finset.eq_univ_of_forall
  intro y
  let J := Finset.univ.filter (fun i => x i ≠ y i)
  have he : Cube.flip J x = y := by
    funext i
    cases h₁ : x i <;> cases h₂ : y i <;> simp [J, Cube.flip, h₁, h₂]
  exact he ▸ closed J

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Grouping trivial sites and shared labels
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral

variable {K S T : Type} [Field K] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

namespace Raw

theorem group_pad (f : S ⊕ T → S) (h : ∀ s, f (.inl s) = s) (A : Raw K S) :
    (pad T A).group f ≈ A := by
  let src (s : S) : Fiber f s := ⟨.inl s, h s⟩
  let B := (pad T A).group f
  let get (s : S) (x : B.leg s) : A.leg s := x (src s)
  have hg (s : S) : Function.Surjective (get s) := by
    intro x
    let y : B.leg s := fun t => match t with
      | ⟨.inl u, hu⟩ => ((h u).symm.trans hu).symm ▸ x
      | ⟨.inr _, _⟩ => ()
    exact ⟨y, rfl⟩
  have he (s : S) (x : B.leg s) (i : A.term) : B.factor i s x = A.factor i s (get s x) := by
    change (∏ t : Fiber f s, (pad T A).factor i t (x t)) = _
    rw [Fintype.prod_eq_single (src s)]
    · rfl
    · rintro ⟨u | u, hu⟩ hn
      · exact False.elim (hn (Subtype.ext (congrArg Sum.inl ((h u).symm.trans hu))))
      · rfl
  change B ≈ A
  refine ⟨.rows (Equiv.refl _) (fun s x => ?_), .rows (Equiv.refl _) fun s x => .inl ⟨_, he s x⟩⟩
  obtain ⟨y, rfl⟩ := hg s x
  exact .inl ⟨y, fun i => (he s y i).symm⟩

omit [DecidableEq S] in
private theorem label_rows {A B : Raw K S} [∀ s, DecidableEq (A.leg s)]
    [∀ s, DecidableEq (B.leg s)] (e : B.term ≃ A.term)
    (a : ∀ s, A.term → A.leg s) (b : ∀ s, B.term → B.leg s)
    (ha : ∀ i s x, A.factor i s x = if x = a s i then 1 else 0)
    (hb : ∀ i s x, B.factor i s x = if x = b s i then 1 else 0)
    (h : ∀ s i j, b s i = b s j ↔ a s (e i) = a s (e j)) : A.Restricts B := by
  refine Restricts.rows e fun s x => ?_
  by_cases hx : ∃ i, x = b s i
  · obtain ⟨i, rfl⟩ := hx
    exact .inl ⟨a s (e i), fun j => by simp only [ha, hb, h]⟩
  · exact .inr (fun i => by rw [hb, ite_eq_right (fun hi => hx ⟨i, hi⟩)])

theorem group_shared (f : T → S) (U : Finset T) (n : ℕ) :
    (shared K U n).group f ≈ shared K (U.image f) n := by
  classical
  let A := (shared K U n).group f
  let B := shared K (U.image f) n
  let a (s : S) (i : Fin n) (t : Fiber f s) := port U t.val i
  let b (s : S) (i : Fin n) := port (U.image f) s i
  have ha (i : Fin n) (s : S) (x : Fiber f s → Fin n) :
      A.factor i s x = if x = a s i then 1 else 0 := by
    change (∏ t, if x t = a s i t then (1 : K) else 0) = _
    by_cases e : x = a s i
    · simp [e]
    · obtain ⟨t, ht⟩ := Function.ne_iff.mp e
      rw [ite_eq_right e]
      exact Finset.prod_eq_zero (Finset.mem_univ t) (ite_eq_right ht)
  have hb (i : Fin n) (s : S) (x : Fin n) :
      B.factor i s x = if x = b s i then 1 else 0 := rfl
  have hl (s : S) (i j : Fin n) : b s i = b s j ↔ a s i = a s j := by
    by_cases hs : s ∈ U.image f
    · obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hs
      simp only [b, port, ite_eq_left hs]
      refine ⟨fun h => congrArg _ h, fun h => ?_⟩
      simpa [a, port, ht] using congrFun h ⟨t, he⟩
    · have hz (t : Fiber f s) : t.val ∉ U :=
        fun h => hs (Finset.mem_image.mpr ⟨t, h, t.property⟩)
      exact iff_of_true (by simp only [b, port, ite_eq_right hs]) (by funext t; simp [a, port, hz])
  let _ : ∀ s, DecidableEq (A.leg s) := fun s => (inferInstance : DecidableEq (Fiber f s → Fin n))
  let _ : ∀ s, DecidableEq (B.leg s) := fun _ => (inferInstance : DecidableEq (Fin n))
  change A ≈ B
  exact ⟨label_rows (Equiv.refl _) a b ha hb hl,
    label_rows (Equiv.refl _) b a hb ha (fun s i j => (hl s i j).symm)⟩

end Raw

namespace Tensor

theorem group_pad [Nonempty S] (f : S ⊕ T → S) (hf : Function.Surjective f)
    (h : ∀ s, f (.inl s) = s) (A : Tensor K S) :
    group f hf (pad T A) = A :=
  Quotient.inductionOn A fun a => ofRaw_eq (Raw.group_pad f h a)

theorem group_shared (f : T → S) (hf : Function.Surjective f) (U : Finset T) (n : ℕ) :
    group f hf (shared K U n) = shared K (U.image f) n :=
  ofRaw_eq (Raw.group_shared f U n)

theorem group_wire (f : T → S) (hf : Function.Surjective f) (a b : T) (n : ℕ) :
    group f hf (wire K a b n) = wire K (f a) (f b) n := by
  simpa [wire] using group_shared (K := K) f hf {a, b} n

end Tensor
end OAI.LinearAlgebra.MatrixExponent.Spectral
end

/-!
# Arbitrary placements

Sites outside the image have trivial legs. Placement is multiplicative
and functorial. Additivity is only used for surjective site maps.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral

variable {K S T R : Type} [Field K] [Fintype S] [Fintype T] [Fintype R]
  [DecidableEq S] [DecidableEq T] [DecidableEq R]

namespace Raw

theorem integral_group_id {O : Subring K} (A : Raw K S) :
    (Valued.equiv O).r (A.group id) A := by
  constructor
  · refine .pullback (fun s x t => cast (congrArg A.leg t.property.symm) x) fun x => ?_
    erw [coeff_group]
    rfl
  · exact .pullback (fun s x => x ⟨s, rfl⟩) (coeff_group id A)

theorem group_id (A : Raw K S) : A.group id ≈ A :=
  Valued.forget_equiv (integral_group_id (O := ⊤) A)

theorem integral_group_comp {O : Subring K} (f : T → S) (g : R → T) (A : Raw K R) :
    (Valued.equiv O).r (A.group (f ∘ g)) ((A.group g).group f) := by
  constructor
  · refine .pullback (fun s x t => x ⟨g t, t.property⟩ ⟨t, rfl⟩) fun x => ?_
    erw [coeff_group, coeff_group, coeff_group]
    rfl
  · refine .pullback (fun s x t r => x ⟨r, (congrArg f r.property).trans t.property⟩)
      fun x => ?_
    erw [coeff_group, coeff_group, coeff_group]
    rfl

theorem group_comp (f : T → S) (g : R → T) (A : Raw K R) :
    A.group (f ∘ g) ≈ (A.group g).group f :=
  Valued.forget_equiv (integral_group_comp (O := ⊤) f g A)

theorem integral_group_inl {O : Subring K} (A : Raw K S) :
    (Valued.equiv O).r (A.group (Sum.inl : S → S ⊕ T)) (A.pad T) := by
  let f : S → S ⊕ T := Sum.inl
  let F (s : S ⊕ T) (x : (A.pad T).leg s) : (A.group f).leg s :=
    fun t => cast (congrArg (pad T A).leg t.property.symm) x
  let G (s : S ⊕ T) : (A.group f).leg s → (A.pad T).leg s :=
    match s with
    | .inl a => fun x => x ⟨a, rfl⟩
    | .inr _ => fun _ => ()
  constructor
  · refine .pullback F fun x => ?_
    rw [pad_coeff, coeff_group]
    rfl
  · refine .pullback G fun x => ?_
    rw [coeff_group, pad_coeff]

theorem group_inl (A : Raw K S) : A.group (Sum.inl : S → S ⊕ T) ≈ A.pad T :=
  Valued.forget_equiv (integral_group_inl (O := ⊤) A)

end Raw

namespace Tensor

def place (f : T → S) : Tensor K T → Tensor K S :=
  Quotient.map (Raw.group f) fun _ _ h => ⟨h.1.group f, h.2.group f⟩

theorem place_ofRaw (f : T → S) (A : Raw K T) :
    place f (ofRaw A) = ofRaw (A.group f) := rfl

theorem place_eq_group (f : T → S) (hf : Function.Surjective f) (A : Tensor K T) :
    place f A = group f hf A := rfl

theorem place_mono (f : T → S) : Monotone (place (K := K) f) :=
  fun A B => Quotient.inductionOn₂ A B fun _ _ h => Raw.Restricts.group h f

theorem place_zero (f : T → S) : place f (0 : Tensor K T) = 0 := ofRaw_eq (Raw.group_zero f)
theorem place_one (f : T → S) : place f (1 : Tensor K T) = 1 := ofRaw_eq (Raw.group_one f)

theorem place_mul (f : T → S) (A B : Tensor K T) :
    place f (A * B) = place f A * place f B :=
  Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Raw.group_mul f a b)

theorem place_id (A : Tensor K S) : place id A = A :=
  Quotient.inductionOn A fun a => ofRaw_eq (Raw.group_id a)

theorem place_comp (f : T → S) (g : R → T) (A : Tensor K R) :
    place (f ∘ g) A = place f (place g A) :=
  Quotient.inductionOn A fun a => ofRaw_eq (Raw.group_comp f g a)

theorem place_inl [Nonempty S] (A : Tensor K S) :
    place (Sum.inl : S → S ⊕ T) A = pad T A :=
  Quotient.inductionOn A fun a => ofRaw_eq (Raw.group_inl a)

theorem place_add_le [Nonempty T] (f : T → S) (A B : Tensor K T) :
    place f (A + B) ≤ place f A + place f B := by
  let g : T ⊕ S → S := Sum.elim f id
  have hg : Function.Surjective g := fun s => ⟨.inr s, rfl⟩
  have he (X : Tensor K T) : place f X = group g hg (pad S X) := by
    rw [← place_eq_group, ← place_inl, ← place_comp]
    rfl
  rw [he, he, he, ← (group g hg).map_add]
  exact group_mono g hg ((padding S).add_le A B)

theorem place_shared (f : T → S) (U : Finset T) (n : ℕ) :
    place f (shared K U n) = shared K (U.image f) n :=
  ofRaw_eq (Raw.group_shared f U n)

theorem place_wire (f : T → S) (a b : T) (n : ℕ) :
    place f (wire K a b n) = wire K (f a) (f b) n := by
  simpa [wire] using place_shared (K := K) f {a, b} n

end Tensor
end OAI.LinearAlgebra.MatrixExponent.Spectral
end
