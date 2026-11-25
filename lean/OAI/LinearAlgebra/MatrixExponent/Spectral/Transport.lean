import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import OAI.LinearAlgebra.MatrixExponent.Spectral.Wire
import OAI.LinearAlgebra.TensorSpectrum.CharacterPower
import Mathlib.Analysis.SpecialFunctions.Pow.Real

section
/-!
# Exterior creation and contraction

Use the signed subset basis. Index a degree by its cardinality plus
one, so degree zero has a predecessor with empty basis. Maximizing
the weighted dimension bounds both neighboring dimensions at once.
-/

open Finset

namespace OAI.LinearAlgebra.MatrixExponent.Spectral

private def level (q l : ℕ) : Finset (Finset (Fin q)) :=
  univ.filter (fun x => x.card + 1 = l)

private theorem optimal_level (q : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ l : ℕ, 0 < (level q l).card ∧
      ((level q (l + 1)).card : ℝ) ≤ (level q l).card * r ∧
      ((level q (l - 1)).card : ℝ) * r ≤ (level q l).card := by
  let score (l : ℕ) := ((level q l).card : ℝ) / r ^ l
  obtain ⟨l, _, hmax⟩ := (range (q + 3)).exists_max_image score (by simp)
  have hl : 0 < (level q l).card := by
    have h1 : 0 < (level q 1).card := card_pos.mpr ⟨∅, by simp [level]⟩
    have hs : 0 < score 1 := div_pos (Nat.cast_pos.mpr h1) (pow_pos hr _)
    exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right (pow_pos hr l)).mp
      (hs.trans_le (hmax 1 (by simp))))
  obtain ⟨x, hx⟩ := card_pos.mp hl
  have hx' := (mem_filter.mp hx).2
  have hq : x.card ≤ q := by simpa using card_le_univ x
  refine ⟨l, hl, ?_, ?_⟩
  · have h := (div_le_div_iff₀ (pow_pos hr _) (pow_pos hr _)).mp
      (hmax (l + 1) (mem_range.mpr (by omega)))
    apply (mul_le_mul_iff_left₀ (pow_pos hr l)).mp
    simpa only [pow_succ', ← mul_assoc] using h
  · have h := (div_le_div_iff₀ (pow_pos hr _) (pow_pos hr _)).mp
      (hmax (l - 1) (mem_range.mpr (by omega)))
    have heq : r ^ l = r * r ^ (l - 1) := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    apply (mul_le_mul_iff_left₀ (pow_pos hr (l - 1))).mp
    simpa only [heq, ← mul_assoc] using h

variable {q : ℕ} (K : Type) [Field K]

private def sign (i : Fin q) (x : Finset (Fin q)) : K :=
  (-1) ^ (x.filter (· < i)).card

private theorem sign_sq (i : Fin q) (x : Finset (Fin q)) :
    sign K i x * sign K i x = 1 := by
  simp [sign, ← mul_pow]

private theorem sign_insert {i j : Fin q} {x : Finset (Fin q)} (hj : j ∉ x) :
    sign K i (insert j x) = if j < i then -sign K i x else sign K i x := by
  have h : j ∉ x.filter (· < i) := fun hj' => hj (mem_filter.mp hj').1
  by_cases e : j < i <;> simp [sign, filter_insert, e, h, pow_succ]

private theorem sign_erase {i j : Fin q} {x : Finset (Fin q)} (hj : j ∈ x) :
    sign K i (x.erase j) = if j < i then -sign K i x else sign K i x := by
  have h := sign_insert K (i := i) (j := j) (x := x.erase j) (by simp)
  rw [insert_erase hj] at h
  by_cases e : j < i <;> simp [e, h]

private def create (i : Fin q) (x y : Finset (Fin q)) : K :=
  if i ∈ x then 0 else if insert i x = y then sign K i x else 0

private def contract (i : Fin q) (x y : Finset (Fin q)) : K :=
  if i ∈ x then if x.erase i = y then sign K i x else 0 else 0

private theorem anticommutator {l : ℕ} (i j : Fin q) (x y : Finset (Fin q)) (hx : x ∈ level q l) :
    (∑ z ∈ level q (l + 1), create K i x z * contract K j z y) +
    (∑ z ∈ level q (l - 1), contract K j x z * create K i z y) =
    if i = j ∧ x = y then 1 else 0 := by
  have hx' := (mem_filter.mp hx).2
  have hu : (∑ z ∈ level q (l + 1), create K i x z * contract K j z y) =
      if i ∈ x then 0 else sign K i x * contract K j (insert i x) y := by
    by_cases hi : i ∈ x
    · simp [create, hi]
    · have ht : insert i x ∈ level q (l + 1) := by simp [level, hi, hx']
      simp [create, hi, ite_mul, ht]
  have hd : (∑ z ∈ level q (l - 1), contract K j x z * create K i z y) =
      if j ∈ x then sign K j x * create K i (x.erase j) y else 0 := by
    by_cases hj : j ∈ x
    · have ht : x.erase j ∈ level q (l - 1) := by
        have := card_erase_add_one hj
        exact mem_filter.mpr ⟨mem_univ _, by omega⟩
      simp [contract, hj, ite_mul, ht]
    · simp [contract, hj]
  rw [hu, hd]
  by_cases he : i = j
  · subst j
    by_cases hi : i ∈ x
    · simp [hi, create, insert_erase hi, sign_erase K hi, mul_ite, sign_sq]
    · simp [hi, contract, sign_insert K hi, mul_ite, sign_sq]
  · by_cases hi : i ∈ x
    · simp [hi, he, create]
    by_cases hj : j ∈ x
    · rw [ite_eq_right hi, ite_eq_left hj]
      simp only [contract, create, mem_erase, mem_insert, hj, hi, or_true, and_false,
        ite_false, ite_true, erase_insert_of_ne he, sign_insert K hi, sign_erase K hj,
        he, false_and]
      by_cases ht : insert i (x.erase j) = y
      · rcases lt_or_gt_of_ne he with h | h <;> simp [ht, h, h.not_gt, mul_comm]
      · simp [ht]
    · simp [hi, hj, he, Ne.symm he, contract]

private noncomputable def entry (s : Finset (Finset (Fin q))) (i : Fin s.card) : Finset (Fin q) :=
  (s.equivFin.symm i).val

private theorem sum_entry (s : Finset (Finset (Fin q))) (f : Finset (Fin q) → K) :
    (∑ i, f (entry s i)) = ∑ x ∈ s, f x :=
  (s.equivFin.symm.sum_comp (fun x => f x.val)).trans (sum_coe_sort s f)

/-- The two orders of creation and contraction sum to the identity
for equal labels and to zero for unequal labels, in every characteristic. -/
theorem exterior (q : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ H P M : ℕ, 0 < H ∧ (P : ℝ) ≤ H * r ∧ (M : ℝ) * r ≤ H ∧
    ∃ (L : Fin q → Fin H → Fin P → K) (D : Fin q → Fin P → Fin H → K)
      (A : Fin q → Fin H → Fin M → K) (B : Fin q → Fin M → Fin H → K),
      ∀ i j x y, (∑ z, L i x z * D j z y) + (∑ z, A j x z * B i z y) =
        if i = j ∧ x = y then 1 else 0 := by
  obtain ⟨l, hH, hP, hM⟩ := optimal_level q r hr
  let H := level q l
  let P := level q (l + 1)
  let M := level q (l - 1)
  refine ⟨H.card, P.card, M.card, hH, hP, hM,
    fun i x z => create K i (entry H x) (entry P z),
    fun j z y => contract K j (entry P z) (entry H y),
    fun j x z => contract K j (entry H x) (entry M z),
    fun i z y => create K i (entry M z) (entry H y), ?_⟩
  intro i j x y
  have he : Function.Injective (entry H) := Subtype.val_injective.comp H.equivFin.symm.injective
  rw [sum_entry K P (fun z => create K i (entry H x) z * contract K j z (entry H y)),
      sum_entry K M (fun z => contract K j (entry H x) z * create K i z (entry H y))]
  simpa only [he.eq_iff] using
    anticommutator K i j (entry H x) (entry H y) (H.equivFin.symm x).property

end OAI.LinearAlgebra.MatrixExponent.Spectral
end

/-! # Joining shared labels by local equality tests -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

open Raw (port)
variable (K : Type) [Field K] {S : Type} [Fintype S] [DecidableEq S]

theorem shared_subset {U V : Finset S} (h : U ⊆ V) (n : ℕ) :
    shared K U n ≤ shared K V n := by
  let L (s : S) (x y : Fin n) := if x = port U s y then (1 : K) else 0
  refine ⟨L, fun x => ?_⟩
  change S → Fin n at x
  change (∑ i : Fin n, ∏ s, if x s = port U s i then (1 : K) else 0) =
    ∑ i : Fin n, ∏ s, ∑ y, L s (x s) y * if y = port V s i then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, L]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro s _
  by_cases hs : s ∈ U
  · simp [port, hs, h hs]
  · simp [port, hs]

theorem shared_join {U V : Finset S} {c : S} (hu : c ∈ U) (hv : c ∈ V) (n : ℕ) :
    shared K (U ∪ V) n ≤ shared K U n * shared K V n := by
  let L (s : S) (x : Fin n) (y : Fin n × Fin n) :=
    if (s = c → y.1 = y.2) ∧ x = (if s ∈ U then y.1 else y.2) then (1 : K) else 0
  refine ⟨L, fun x => ?_⟩
  change S → Fin n at x
  change (∑ i : Fin n, ∏ s, if x s = port (U ∪ V) s i then (1 : K) else 0) =
    ∑ ij : Fin n × Fin n, ∏ s, ∑ y, L s (x s) y *
      ((if y.1 = port U s ij.1 then 1 else 0) * (if y.2 = port V s ij.2 then 1 else 0))
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_eq_single i]
  · apply Finset.prod_congr rfl
    intro s _
    by_cases e : s = c
    · subst s
      simp [L, port, hu, hv]
    · by_cases hs : s ∈ U <;> simp [L, port, hs, e]
  · intro j hj
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp [L, port, hu, hv, hj.symm]

theorem wire_triangle (a b c : S) (n : ℕ) :
    wire K a c n ≤ wire K a b n * wire K b c n :=
  (shared_subset K (by simp [Finset.insert_subset_iff]) n).trans
    (shared_join K (c := b) (U := {a, b}) (V := {b, c}) (by simp) (by simp) n)

theorem wire_self (a : S) {n : ℕ} (hn : 0 < n) : wire K a a n = 1 := by
  apply le_antisymm _ (one_le_wire K a a hn)
  let L (s : S) (x : Fin n) (_ : Unit) :=
    if s = a ∨ x.val = 0 then (1 : K) else 0
  refine ⟨L, fun x => ?_⟩
  change S → Fin n at x
  change (∑ i : Fin n, ∏ s, if x s = port {a, a} s i then (1 : K) else 0) =
    ∑ _ : Unit, ∏ s, ∑ j : Unit, L s (x s) j * 1
  rw [Fintype.sum_eq_single (x a)]
  · simp only [Fintype.sum_unique, mul_one]
    apply Finset.prod_congr rfl
    intro s _
    by_cases hs : s = a <;> simp [L, port, hs, Fin.ext_iff]
  · intro i hi
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [port, hi.symm]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Restriction using shared indices

Each assignment of shared indices exposes a label at each site. Local
maps may read the label, select an input coordinate and apply a scalar.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
open Classical

variable {K S X Y I J L M : Type} [Field K] [Fintype S] [Nonempty S]
  [Fintype X] [Fintype Y] [Fintype I] [Fintype J] [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]

def array (f : (S → X) → K) : Tensor K S := ofRaw (Raw.ofTable (fun _ => X) f)

def signals (K : Type) [Field K] (e : S → I → L) : Tensor K S :=
  ofRaw ⟨fun _ => L, I, fun i s x => if x = e s i then 1 else 0⟩

omit [Nonempty S] in
theorem signals_wire [DecidableEq S] (a b : S) (n : ℕ) :
    signals K (Raw.port (n := n) {a, b}) = wire K a b n := rfl

omit [Nonempty S] in
theorem signals_mul (e : S → I → L) (f : S → J → M) :
    signals K (fun s (i : I × J) => (e s i.1, f s i.2)) = signals K e * signals K f := by
  apply ofRaw_eq
  refine Raw.relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i s x => ?_
  change I × J at i
  change L × M at x
  change (if x = (e s i.1, f s i.2) then (1 : K) else 0) =
    (if x.1 = e s i.1 then 1 else 0) * (if x.2 = f s i.2 then 1 else 0)
  simp only [Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul]

theorem use_signals (A : (S → X) → K) (B : (S → Y) → K) (e : S → I → L)
    (v : S → Y → L → K) (g : S → Y → L → X)
    (h : ∀ y, B y = ∑ i, (∏ s, v s (y s) (e s i)) * A (fun s => g s (y s) (e s i))) :
    array B ≤ array A * signals K e := by
  let P := Raw.ofTable (fun _ => X) A
  let Q := Raw.ofTable (fun _ => Y) B
  let f (s : S) (y : Y) (p : X × L) := if p.1 = g s y p.2 then v s y p.2 else 0
  refine ⟨f, fun y => ?_⟩
  change S → Y at y
  change Q.coeff y = ∑ t : P.term × I, ∏ s, ∑ p : X × L, f s (y s) p *
    (P.factor t.1 s p.1 * if p.2 = e s t.2 then 1 else 0)
  rw [show Q.coeff y = B y from Raw.coeff_ofTable _ _ _, h]
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, f, ite_mul, zero_mul, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  congr 1
  exact (Raw.coeff_ofTable _ A _).symm

theorem array_pullback (A : (S → X) → K) (B : (S → Y) → K) (g : S → Y → X)
    (h : ∀ y, B y = A (fun s => g s (y s))) : array B ≤ array A := by
  apply Raw.Restricts.pullback g
  intro y
  exact (Raw.coeff_ofTable _ B _).trans ((h y).trans (Raw.coeff_ofTable _ A _).symm)

theorem array_mul (A : (S → X) → K) (B : (S → Y) → K) :
    array (fun y : S → X × Y => A (fun s => (y s).1) * B (fun s => (y s).2)) =
      array A * array B := by
  apply ofRaw_eq
  refine Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
  rw [Raw.coeff_mul]
  change S → X × Y at x
  exact (Raw.coeff_ofTable _ _ x).trans
    (congrArg₂ (· * ·) (Raw.coeff_ofTable _ A _).symm (Raw.coeff_ofTable _ B _).symm)

theorem array_sum (A B : (S → X) → K) : array (fun y => A y + B y) ≤ array A + array B := by
  let P := Raw.ofTable (fun _ => X) A
  let Q := Raw.ofTable (fun _ => X) B
  let f (_ : S) (x : X) (y : X ⊕ X) := if Sum.elim id id y = x then (1 : K) else 0
  refine ⟨f, fun x => ?_⟩
  change S → X at x
  change (Raw.ofTable _ _).coeff x = ∑ t : P.term ⊕ Q.term, ∏ s,
    ∑ y : X ⊕ X, f s (x s) y * (P + Q).factor t s y
  simp only [Raw.coeff_ofTable, Fintype.sum_sum_type]
  change _ = (∑ t : P.term, ∏ s, ((∑ y, f s (x s) (.inl y) * P.factor t s y) +
      ∑ y, f s (x s) (.inr y) * 0)) +
    ∑ t : Q.term, ∏ s, ((∑ y, f s (x s) (.inl y) * 0) +
      ∑ y, f s (x s) (.inr y) * Q.factor t s y)
  have hf (z : X) (q : X → K) : (∑ y, (if y = z then (1 : K) else 0) * q y) = q z :=
    by simp [ite_mul]
  simp only [f, Sum.elim_inl, Sum.elim_inr, id_eq, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add]
  change _ = (∑ t : P.term, ∏ s, ∑ y : X, (if y = x s then 1 else 0) * P.factor t s y) +
    ∑ t : Q.term, ∏ s, ∑ y : X, (if y = x s then 1 else 0) * Q.factor t s y
  refine (congrArg₂ (· + ·) (Raw.coeff_ofTable _ A x).symm (Raw.coeff_ofTable _ B x).symm).trans ?_
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.prod_congr rfl <;> intro s _ <;> exact (hf (x s) _).symm

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-! # Equality of marked indices as a wire -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]

omit [DecidableEq S] [Nonempty S] in
private theorem weighted_pullback (P Q : Raw K S) (g : ∀ s, Q.leg s → P.leg s)
    (v : ∀ s, Q.leg s → K)
    (h : ∀ x, Q.coeff x = (∏ s, v s (x s)) * P.coeff (fun s => g s (x s))) :
    ofRaw Q ≤ ofRaw P := by
  classical
  refine ⟨fun s x y => if y = g s x then v s x else 0, fun x => ?_⟩
  rw [h, Raw.coeff, Finset.mul_sum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.prod_mul_distrib]

abbrev Slot (X : Type) (q : ℕ) := X × Fin q × Fin q

/-- Inactive indices may be ignored instead of fixed to zero. -/
def link (K : Type) [Field K] (a b : S) (q : ℕ) (x : S → Slot Unit q) : K :=
  if (x a).2.1 = (x b).2.2 then 1 else 0

theorem array_link (a b : S) (q : ℕ) : array (link K a b q) = wire K a b q := by
  classical
  apply le_antisymm
  · let L (s : S) (x : Slot Unit q) (y : Fin q) : K :=
      (if s = a then if x.2.1 = y then 1 else 0 else 1) *
      (if s = b then if x.2.2 = y then 1 else 0 else 1)
    refine ⟨L, fun x => ?_⟩
    change S → Slot Unit q at x
    rw [Raw.coeff_ofTable]
    change link K a b q x = ∑ i : Fin q, ∏ s, ∑ j, L s (x s) j *
      if j = Raw.port {a, b} s i then 1 else 0
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [L, Finset.prod_mul_distrib]
    simp [Raw.port, link, mul_ite]
  · let v (s : S) (x : Fin q) := if s = a ∨ s = b ∨ x.val = 0 then (1 : K) else 0
    apply weighted_pullback _ _ (fun _ (x : Fin q) => ((), x, x)) v
    intro x
    change S → Fin q at x
    rw [Raw.coeff_ofTable]
    change (∑ i : Fin q, ∏ s, if x s = Raw.port {a, b} s i then (1 : K) else 0) =
      (∏ s, v s (x s)) * if x a = x b then 1 else 0
    rw [Fintype.sum_eq_single (x a)]
    · by_cases e : x a = x b
      · rw [ite_eq_left e, mul_one]
        apply Finset.prod_congr rfl
        intro s _
        by_cases ha : s = a
        · simp [Raw.port, v, ha]
        by_cases hb : s = b
        · simp [Raw.port, v, hb, e]
        simp [Raw.port, v, ha, hb, Fin.ext_iff]
      · rw [ite_eq_right e, mul_zero]
        apply Finset.prod_eq_zero (Finset.mem_univ b)
        simp [Raw.port, Ne.symm e]
    · intro i hi
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [Raw.port, hi.symm]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Splitting an array with two marked indices

The first index passes through a kernel, with two catalyst indices
held at the endpoints. The second index is unchanged. Each inequality
below is a local linear restriction, also when some sites coincide.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

abbrev Marked (K S X : Type) (q : ℕ) := (S → X) → Fin q → Fin q → K
abbrev Kernel (K : Type) (q H : ℕ) := Fin q → Fin q → Fin H → Fin H → K

variable {K S X : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S] [Fintype X]
variable {q H P : ℕ}

def placePair (T : Marked K S X q) (c j : S) (y : S → Slot X q) : K :=
  T (fun s => (y s).1) (y c).2.1 (y j).2.2

def child (T : Marked K S X q) (U : Kernel K q H) (a b : S) :
    Marked K S (Slot X H) q :=
  fun y i j => ∑ k, U i k (y a).2.1 (y b).2.2 * T (fun s => (y s).1) k j

def productKernel (L : Fin q → Fin H → Fin P → K) (D : Fin q → Fin P → Fin H → K) :
    Kernel K q H := fun i k x y => ∑ z, L i x z * D k z y

variable (T : Marked K S X q) (a b c j : S)

omit [DecidableEq S] in
theorem placePair_swap :
    array (placePair (fun y x z => T y z x) c j) = array (placePair T j c) := by
  let g (_ : S) (u : Slot X q) := (u.1, u.2.2, u.2.1)
  exact le_antisymm (array_pullback _ _ g fun _ => rfl) (array_pullback _ _ g fun _ => rfl)

omit [DecidableEq S] in
theorem child_flip (U : Kernel K q H) :
    array (placePair (child T (fun i k x y => U i k y x) a b) c j) =
      array (placePair (child T U b a) c j) := by
  let g (_ : S) (u : Slot (Slot X H) q) := ((u.1.1, u.1.2.2, u.1.2.1), u.2)
  exact le_antisymm (array_pullback _ _ g fun _ => rfl) (array_pullback _ _ g fun _ => rfl)

theorem child_sum (U V : Kernel K q H)
    (h : ∀ i k x y, U i k x y + V i k y x = if i = k ∧ x = y then 1 else 0) :
    array (placePair T c j) * wire K a b H ≤
      array (placePair (child T U a b) c j) + array (placePair (child T V b a) c j) := by
  rw [← child_flip T a b c j V, ← array_link a b H, ← array_mul]
  refine le_trans ?_ (array_sum _ _)
  let g (_ : S) (x : Slot X q × Slot Unit H) := ((x.1.1, x.2.2), x.1.2)
  apply array_pullback _ _ g
  intro x
  simp only [placePair, child, g, ← Finset.sum_add_distrib, ← add_mul, h, link]
  simp [ite_and, ite_mul, mul_ite]

theorem child_here (hq : 0 < q) (U : Kernel K q H) :
    array (placePair (child T U a b) a j) ≤ array (placePair T a j) * wire K a b H := by
  let e (s : S) (i : Fin q × Fin H) :=
    (Raw.port {a, a} s i.1, Raw.port {a, b} s i.2)
  have he : signals K e = wire K a b H := by
    rw [show signals K e = _ from signals_mul (Raw.port {a, a}) (Raw.port {a, b}),
      signals_wire, signals_wire, wire_self K a hq, one_mul]
  rw [← he]
  let v (s : S) (y : Slot (Slot X H) q) (i : Fin q × Fin H) :=
    (if s = a then U y.2.1 i.1 y.1.2.1 i.2 else 1) *
    (if s = b then if i.2 = y.1.2.2 then 1 else 0 else 1)
  apply use_signals _ _ e v (fun _ y i => (y.1.1, i.1, y.2.2))
  intro y
  simp only [Fintype.sum_prod_type, v, Finset.prod_mul_distrib]
  simp [e, Raw.port, placePair, child, mul_ite, ite_mul]

theorem child_cross (hq : 0 < q) (L : Fin q → Fin H → Fin P → K)
    (D : Fin q → Fin P → Fin H → K) :
    array (placePair (child T (productKernel L D) a b) c j) ≤
      array (placePair T b j) * (wire K a c H * wire K c b P) := by
  let e' (s : S) (i : Fin P × Fin H) := (Raw.port {c, b} s i.1, Raw.port {a, c} s i.2)
  let e (s : S) (i : Fin q × Fin P × Fin H) := (Raw.port {b, b} s i.1, e' s i.2)
  have he : signals K e = wire K a c H * wire K c b P := by
    rw [show signals K e = _ from signals_mul (Raw.port {b, b}) e',
      show signals K e' = _ from signals_mul (Raw.port {c, b}) (Raw.port {a, c}),
      signals_wire, signals_wire, signals_wire, wire_self K b hq, one_mul, mul_comm]
  rw [← he]
  let v (s : S) (y : Slot (Slot X H) q) (i : Fin q × Fin P × Fin H) :=
    (if s = c then L y.2.1 i.2.2 i.2.1 else 1) *
    (if s = b then D i.1 i.2.1 y.1.2.2 else 1) *
    (if s = a then if i.2.2 = y.1.2.1 then 1 else 0 else 1)
  apply use_signals _ _ e v (fun _ y i => (y.1.1, i.1, y.2.2))
  intro y
  simp only [Fintype.sum_prod_type, v, Finset.prod_mul_distrib]
  simp [e, e', Raw.port, placePair, child, productKernel, Finset.sum_mul, mul_ite, ite_mul]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-! # The wire pseudometric of a spectral point -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S]

def dist (f : Tensor K S →+* ℝ) (a b : S) : ℝ :=
  Real.log (f (wire K a b 2)) / Real.log 2

variable (f : Tensor K S →+* ℝ)

theorem dist_self (a : S) : dist f a a = 0 := by
  simp [dist, wire_self K a (n := 2) (by decide)]

theorem dist_comm (a b : S) : dist f a b = dist f b a := by
  unfold dist
  rw [wire_comm K a b]

variable (hf : Monotone f)
include hf

private theorem price_bounds (a b : S) {n : ℕ} (hn : 0 < n) :
    1 ≤ f (wire K a b n) ∧ f (wire K a b n) ≤ (n : ℝ) := by
  refine ⟨by simpa using hf (one_le_wire K a b hn), ?_⟩
  have h : wire K a b n ≤ (n : Tensor K S) := by
    rw [← shared_all K n]
    exact shared_subset K (Finset.subset_univ _) n
  simpa using hf h

theorem dist_nonneg (a b : S) : 0 ≤ dist f a b :=
  div_nonneg (Real.log_nonneg (price_bounds f hf a b (by decide)).1)
    (Real.log_nonneg (by norm_num))

theorem dist_le_one (a b : S) : dist f a b ≤ 1 := by
  have h := price_bounds f hf a b (n := 2) (by decide)
  exact (div_le_one (Real.log_pos (by norm_num))).mpr
    (Real.log_le_log (zero_lt_one.trans_le h.1) (by simpa using h.2))

theorem price_wire (a b : S) {n : ℕ} (hn : 0 < n) :
    f (wire K a b n) = (n : ℝ) ^ dist f a b := by
  obtain ⟨p, _, _, hp⟩ := TensorSpectrum.exists_power_of_monotone_multiplicative
    (fun k => f (wire K a b k))
    (fun m n _ _ => (congrArg f (shared_mul K {a, b} m n)).trans (f.map_mul _ _))
    (fun _ _ _ h => hf (wire_mono K a b h)) (fun _ h => price_bounds f hf a b h)
  have hp2 := hp 2 (by decide)
  have hd : dist f a b = p := by
    unfold dist
    rw [hp2, Nat.cast_ofNat, Real.log_rpow (by norm_num : (0 : ℝ) < 2),
      mul_div_cancel_right₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [hd]
  exact hp n hn

theorem dist_triangle (a b c : S) : dist f a c ≤ dist f a b + dist f b c := by
  have h := hf (wire_triangle K a b c 2)
  rw [f.map_mul] at h
  simp only [price_wire f hf _ _ (n := 2) (by decide), Nat.cast_ofNat,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

section
/-! # Price inequalities for a pair of marked indices -/

namespace OAI.LinearAlgebra.MatrixExponent.Spectral

/-- `V` consists of scaled prices as functions of the two placements.
The split uses an exterior-algebra index at the endpoints `a, b`. -/
structure Splitting {S : Type} (d : S → S → ℝ) (V : (S → S → ℝ) → Prop) : Prop where
  self : ∀ a, d a a = 0
  comm : ∀ a b, d a b = d b a
  triangle : ∀ a b c, d a c ≤ d a b + d b c
  nonneg : ∀ a b, 0 ≤ d a b
  wire : ∀ n : ℕ, 0 < n → V (fun a b => (n : ℝ) ^ d a b)
  swap : ∀ f, V f → V (fun a b => f b a)
  split : ∀ f, V f → ∀ a b, 0 < d a b → ∀ r : ℝ, 0 < r →
    ∃ u v, V u ∧ V v ∧
      (∀ c j, f c j ≤ u c j + v c j) ∧
      (∀ j, u a j ≤ f a j ∧ v b j ≤ f b j) ∧
      (∀ c j, d a c + d c b = d a b →
        u c j ≤ f b j * r ^ d c b ∧ v c j ≤ f a j * r ^ (-d a c))

end OAI.LinearAlgebra.MatrixExponent.Spectral
end

section
/-!
# Convexity of distances between points on metric intervals

In the matrix of four endpoint exponents, keep the diagonal fixed.
On each branch of a split, updating just one off-diagonal entry halves
the difference between the two diagonal sums. All costs of splitting
are additive in base-two logarithmic units.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Splitting

private noncomputable def E (a : ℝ) := (2 : ℝ) ^ a

private theorem shift {x a : ℝ} (hx : x ≤ E a) (b : ℝ) : x * E b ≤ E (a + b) := by
  unfold E at *
  rw [Real.rpow_add (by norm_num)]
  exact mul_le_mul_of_nonneg_right hx (by positivity)

private theorem combine {x y z a : ℝ} (h : x ≤ y + z) (hy : y ≤ E a) (hz : z ≤ E a) :
    x ≤ E (a + 1) := by
  unfold E at *
  rw [Real.rpow_add_one (by norm_num), mul_two]
  exact h.trans (add_le_add hy hz)

variable {S : Type} {d : S → S → ℝ} {V : (S → S → ℝ) → Prop}
variable (H : Splitting d V) {a b c s t x : S} {f : S → S → ℝ} {p : ℝ}

include H

private theorem split_shift (hf : V f) (hab : 0 < d a b) (g : ℝ) :
    ∃ u v, V u ∧ V v ∧
      (∀ c j, f c j ≤ u c j + v c j) ∧
      (∀ j, u a j ≤ f a j ∧ v b j ≤ f b j) ∧
      (∀ c j p, d a c = p * d a b → d c b = (1 - p) * d a b →
        u c j ≤ f b j * E ((1 - p) * g) ∧ v c j ≤ f a j * E (-p * g)) := by
  let r := E (g / d a b)
  obtain ⟨u, v, hu, hv, hsum, hend, hcross⟩ := H.split f hf a b hab r (by unfold r E; positivity)
  have pow_eq (z : ℝ) : r ^ (z * d a b) = E (z * g) := by
    unfold r E
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    field_simp
  refine ⟨u, v, hu, hv, hsum, hend, fun c j p hc hc' => ?_⟩
  have h := hcross c j (by rw [hc, hc']; ring)
  simpa only [hc, hc', ← neg_mul, pow_eq] using h

private theorem interpolate (hf : V f) (hab : 0 < d a b)
    (hc : d a c = p * d a b) (hc' : d c b = (1 - p) * d a b)
    {A B : ℝ} (ha : f a x ≤ E A) (hb : f b x ≤ E B) :
    f c x ≤ E ((1 - p) * A + p * B + 1) := by
  obtain ⟨u, v, _, _, hsum, _, hcross⟩ := H.split_shift hf hab (A - B)
  obtain ⟨hu, hv⟩ := hcross c x p hc hc'
  apply combine (hsum c x)
  · rw [show (1 - p) * A + p * B = B + (1 - p) * (A - B) by ring]
    exact hu.trans (shift hb _)
  · rw [show (1 - p) * A + p * B = A + -p * (A - B) by ring]
    exact hv.trans (shift ha _)

private theorem halve (hab : 0 < d a b) (hst : 0 < d s t)
    (hc : d a c = p * d a b) (hc' : d c b = (1 - p) * d a b)
    (hx : d s x = p * d s t) (hx' : d x t = (1 - p) * d s t)
    (k : ℕ) (hf : V f) {A B C D : ℝ}
    (hA : f a s ≤ E A) (hB : f a t ≤ E B) (hC : f b s ≤ E C) (hD : f b t ≤ E D) :
    f c x ≤ E ((1 - p) * A + p * D + p * (1 - p) * (B + C - A - D) / 2 ^ k + 2 + k) := by
  induction k generalizing f B C with
  | zero =>
    have ha := H.interpolate (H.swap f hf) hst hx hx' hA hB
    have hb := H.interpolate (H.swap f hf) hst hx hx' hC hD
    convert H.interpolate hf hab hc hc' ha hb using 2
    ring
  | succ k ih =>
    let g := (A - C + B - D) / 2
    obtain ⟨u, v, hu, hv, hsum, hend, hcross⟩ := H.split_shift hf hab g
    have left (j : S) : u a j ≤ f b j * E g ∧ v a j ≤ f a j := by
      simpa [E] using hcross a j 0 (by simp [H.self]) (by simp)
    have right (j : S) : u b j ≤ f b j ∧ v b j ≤ f a j * E (-g) := by
      simpa [E] using hcross b j 1 (by simp) (by simp [H.self])
    rw [Nat.cast_succ, ← add_assoc]
    apply combine (hsum c x)
    · have h := ih hu ((hend s).1.trans hA) ((left t).1.trans (shift hD g))
        ((right s).1.trans hC) ((right t).1.trans hD)
      convert h using 2
      unfold g
      rw [pow_succ]
      ring
    · have h := ih hv ((left s).2.trans hA) ((left t).2.trans hB)
        ((right s).2.trans (shift hA (-g))) ((hend t).2.trans hD)
      convert h using 2
      unfold g
      rw [pow_succ]
      ring

private theorem scaled (n : ℕ) : V (fun a b => E (n * d a b)) := by
  simpa only [E, Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), Nat.cast_pow, Nat.cast_ofNat]
    using H.wire (2 ^ n) (by positivity)

omit H in
private theorem slope {A B C : ℝ} (h : ∀ n : ℕ, E (n * A) ≤ E (n * B + C)) : A ≤ B := by
  by_contra! hAB
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (A - B))
  have hn' := (div_lt_iff₀ (sub_pos.mpr hAB)).mp hn
  have he := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp (h n)
  linarith

private theorem same (h : d a b = 0) (z : S) : d a z = d b z := by
  linarith [H.triangle a b z, H.triangle b a z, H.comm b a]

private theorem one_segment
    (hc : d a c = p * d a b) (hc' : d c b = (1 - p) * d a b) (y : S) :
    d c y ≤ (1 - p) * d a y + p * d b y := by
  rcases (H.nonneg a b).eq_or_lt with hab | hab
  · rw [← hab, mul_zero] at hc hc'
    rw [H.same hc y, ← H.same hc' y]
    exact le_of_eq (by ring)
  apply slope (C := 1)
  intro n
  convert H.interpolate (x := y) (H.scaled n) hab hc hc' le_rfl le_rfl using 2
  ring

/-- Points at the same fraction on two intervals satisfy Busemann convexity.
Neither existence of intermediate points nor separation of sites is required. -/
theorem busemann
    (hc : d a c = p * d a b) (hc' : d c b = (1 - p) * d a b)
    (hx : d s x = p * d s t) (hx' : d x t = (1 - p) * d s t) :
    d c x ≤ (1 - p) * d a s + p * d b t := by
  rcases (H.nonneg a b).eq_or_lt with hab | hab
  · rw [← hab, mul_zero] at hc hc'
    rw [H.same hc s, ← H.same hc' t, H.comm c x, H.comm c s, H.comm c t]
    exact H.one_segment hx hx' c
  rcases (H.nonneg s t).eq_or_lt with hst | hst
  · rw [← hst, mul_zero] at hx hx'
    rw [H.comm a s, H.same hx a, H.comm x a, H.comm b t, ← H.same hx' b, H.comm x b]
    exact H.one_segment hc hc' x
  let A := (1 - p) * d a s + p * d b t
  let R := p * (1 - p) * (d a t + d b s - d a s - d b t)
  have bound (k : ℕ) : d c x ≤ A + R / 2 ^ k := by
    apply slope (C := 2 + k)
    intro n
    convert H.halve hab hst hc hc' hx hx' k (H.scaled n) le_rfl le_rfl le_rfl le_rfl using 2
    unfold A R
    ring
  change d c x ≤ A
  by_contra! h
  obtain ⟨k, hk⟩ := exists_nat_gt (R / (d c x - A))
  have hp : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
  have hz := (div_lt_iff₀ (sub_pos.mpr h)).mp (hk.trans hp)
  have hu := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).mp
    (show d c x - A ≤ R / 2 ^ k by linarith [bound k])
  linarith

theorem unique_midpoint
    (hc : d a c = d a b / 2) (hc' : d c b = d a b / 2)
    (hx : d a x = d a b / 2) (hx' : d x b = d a b / 2) :
    d c x = 0 := by
  have h := H.busemann (a := a) (b := b) (c := c) (s := a) (t := b) (x := x)
    (p := 1 / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [H.self, H.self] at h
  linarith [H.nonneg c x]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Splitting
end

/-!
# Busemann comparison for spectral distances

The exterior creation and contraction identity splits the first
marked index. Dividing both children by the price of the catalyst
gives the three inequalities needed for the halving argument.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S X : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S] [Fintype X]
variable (f : Tensor K S →+* ℝ) (hf : Monotone f)

private def family (p : S → S → ℝ) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (q : ℕ) (_ : 0 < q) (T : Marked K S X q) (w : ℝ),
    0 ≤ w ∧ p = fun a b => w * f (array (placePair T a b))

include hf

omit [Nonempty S] in
private theorem price_at_most (a b : S) {n : ℕ} {v : ℝ} (hn : (n : ℝ) ≤ v) :
    f (wire K a b n) ≤ v ^ dist f a b := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have h := hf (shared_subset K (Finset.subset_univ {a, b}) 0)
    rw [shared_all, Nat.cast_zero, map_zero] at h
    exact h.trans (Real.rpow_nonneg (by simpa using hn) _)
  · rw [price_wire f hf a b h]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hn (dist_nonneg f hf a b)

private theorem price_cross {q H P : ℕ} (hq : 0 < q) (hH : 0 < H) {r : ℝ} (hr : 0 < r)
    (hP : (P : ℝ) ≤ H * r) (T : Marked K S X q)
    (L : Fin q → Fin H → Fin P → K) (D : Fin q → Fin P → Fin H → K)
    (a b c j : S) (hc : dist f a c + dist f c b = dist f a b) :
    f (array (placePair (child T (productKernel L D) a b) c j)) ≤
      (H : ℝ) ^ dist f a b * (f (array (placePair T b j)) * r ^ dist f c b) := by
  have ht : 0 ≤ f (array (placePair T b j)) := by
    simpa only [map_zero] using hf (zero_le (array (placePair T b j)))
  have h := hf (child_cross T a b c j hq L D)
  rw [f.map_mul, f.map_mul, price_wire f hf a c hH] at h
  refine h.trans ?_
  calc
    _ ≤ f (array (placePair T b j)) * ((H : ℝ) ^ dist f a c * ((H : ℝ) * r) ^ dist f c b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (price_at_most f hf c b hP) (by positivity)) ht
    _ = _ := by
      rw [Real.mul_rpow (Nat.cast_nonneg H) hr.le, ← hc,
        Real.rpow_add (by exact_mod_cast hH : (0 : ℝ) < H)]
      ring

private theorem splits : Splitting (dist f) (family f) where
  self := dist_self f
  comm := dist_comm f
  triangle := dist_triangle f hf
  nonneg := dist_nonneg f hf
  wire n hn := by
    refine ⟨Unit, inferInstance, n, hn, fun _ i k => if i = k then 1 else 0, 1,
      zero_le_one, ?_⟩
    funext a b
    change _ = 1 * f (array (link K a b n))
    rw [one_mul, array_link, price_wire f hf a b hn]
  swap _ h := by
    obtain ⟨X, _, q, hq, T, w, hw, rfl⟩ := h
    refine ⟨X, inferInstance, q, hq, fun y i j => T y j i, w, hw, ?_⟩
    funext a b
    rw [placePair_swap]
  split _ h a b _ r hr := by
    obtain ⟨X, _, q, hq, T, w, hw, rfl⟩ := h
    obtain ⟨H, P, M, hH, hP, hM, L, D, A, B, he⟩ := exterior K q r hr
    let U := productKernel L D
    let V := productKernel (fun i y z => B i z y) (fun k z x => A k x z)
    have huv : ∀ i k x y, U i k x y + V i k y x = if i = k ∧ x = y then 1 else 0 := by
      intro i k x y
      simpa only [U, V, productKernel, mul_comm (B _ _ _)] using he i k x y
    let u := child T U a b
    let v := child T V b a
    let t := (H : ℝ) ^ dist f a b
    have ht : 0 < t := Real.rpow_pos_of_pos (by exact_mod_cast hH) _
    let W := w / t
    have hW : 0 ≤ W := div_nonneg hw ht.le
    have hWt : W * t = w := div_mul_cancel₀ _ ht.ne'
    have scale {x y : ℝ} (h : x ≤ t * y) : W * x ≤ w * y := by
      simpa only [← mul_assoc, hWt] using mul_le_mul_of_nonneg_left h hW
    refine ⟨_, _, ⟨_, inferInstance, q, hq, u, W, hW, rfl⟩,
      ⟨_, inferInstance, q, hq, v, W, hW, rfl⟩, ?_, ?_, ?_⟩
    · intro c j
      have h := hf (child_sum T a b c j U V huv)
      rw [f.map_mul, f.map_add, price_wire f hf a b hH] at h
      dsimp only
      rw [← hWt, ← mul_add, mul_assoc, mul_comm t]
      exact mul_le_mul_of_nonneg_left h hW
    · intro j
      have here (a b : S) (k : Kernel K q H) := hf (child_here T a b j hq k)
      constructor
      · apply scale
        simpa only [f.map_mul, price_wire f hf a b hH, mul_comm, t, u] using here a b U
      · apply scale
        simpa only [f.map_mul, price_wire f hf b a hH, dist_comm f b a, mul_comm, t, v]
          using here b a V
    · intro c j hc
      constructor
      · rw [mul_assoc]
        exact scale (price_cross f hf hq hH hr hP T L D a b c j hc)
      · have hc' : dist f b c + dist f c a = dist f b a := by
          rw [dist_comm f b c, dist_comm f c a, add_comm, hc, dist_comm]
        have hm : (M : ℝ) ≤ (H : ℝ) * r⁻¹ := (le_div_iff₀ hr).mpr hM
        have h := price_cross f hf hq hH (inv_pos.mpr hr) hm T (fun i y z => B i z y)
          (fun k z x => A k x z) b a c j hc'
        rw [dist_comm f b a, dist_comm f c a, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le] at h
        rw [mul_assoc]
        exact scale h

theorem busemann {a b c s t x : S} {u : ℝ}
    (hc : dist f a c = u * dist f a b) (hc' : dist f c b = (1 - u) * dist f a b)
    (hx : dist f s x = u * dist f s t) (hx' : dist f x t = (1 - u) * dist f s t) :
    dist f c x ≤ (1 - u) * dist f a s + u * dist f b t :=
  (splits f hf).busemann hc hc' hx hx'

theorem unique_midpoint {a b c x : S}
    (hc : dist f a c = dist f a b / 2) (hc' : dist f c b = dist f a b / 2)
    (hx : dist f a x = dist f a b / 2) (hx' : dist f x b = dist f a b / 2) :
    dist f c x = 0 :=
  (splits f hf).unique_midpoint hc hc' hx hx'

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end
