import OAI.LinearAlgebra.MatrixExponent.BlockProducts
import OAI.LinearAlgebra.MatrixExponent.CircuitCost
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Recursion on blocks and zero padding

A recursive call may have inputs that are already computed values. Work over
an arbitrary algebra `K` with only the constants of `F` supplied for free,
then instantiate `K` with the polynomial ring of the padded problem.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

private def Multiplies (F K : Type*) [CommRing F] [CommRing K] [Algebra F K]
    (i j k cost : ℕ) : Prop :=
  ∀ (S : Set K) (X : Pos i k → K) (Y : Pos k j → K), (∀ x, algebraMap F K x ∈ S) →
    (∀ p, X p ∈ S) → (∀ p, Y p ∈ S) → CanMake S cost (Set.range (mm X Y))

variable {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]

private lemma multiplies_one : Multiplies F K 1 1 1 1 := by
  intro S X Y _ hX hY
  refine (CanMake.mul (hX (0, 0)) (hY (0, 0))).mono_output ?_
  rintro _ ⟨p, rfl⟩
  rw [Subsingleton.elim p (0, 0)]
  simp [mm]

private lemma joinPos_surj {i j d e : ℕ} (u : Pos (i * d) (j * e)) :
    ∃ z p, joinPos z p = u := by
  obtain ⟨⟨x, x'⟩, hx⟩ := finProdFinEquiv.surjective u.1
  obtain ⟨⟨y, y'⟩, hy⟩ := finProdFinEquiv.surjective u.2
  exact ⟨(x, y), (x', y'), Prod.ext hx hy⟩

/-- First form two families of linear combinations, then compute and
recombine the `r` smaller matrix products. -/
private lemma multiplies_step {i j k r d e f cost : ℕ} (h : Integral.Rank F i j k r)
    (ih : Multiplies F K d e f cost) :
    Multiplies F K (i * d) (j * e) (k * f)
      (r * cost + 2 * r * (i * j * (d * e) + i * k * (d * f) + j * k * (e * f))) := by
  intro S X Y hS hX hY
  obtain ⟨a, b, c, hc⟩ := block_formula (K := K) (d := d) (e := e) (f := f) h
  have h0 : (0 : K) ∈ S := by simpa using hS 0
  let A l := linBlock (a l) X
  let B l := linBlock (b l) Y
  have prep {n m u v : ℕ} (g : Fin r → Pos n m → F) (Z : Pos (n * u) (m * v) → K)
      (hZ : ∀ p, Z p ∈ S) :
      CanMake S (r * (u * v * (n * m * 2))) (⋃ l, Set.range (linBlock (g l) Z)) := by
    have entry (l : Fin r) (p : Pos u v) :
        CanMake S (Fintype.card (Pos n m) * 2) {linBlock (g l) Z p} :=
      CanMake.linear h0 (fun z => hS (g l z)) (fun z => hZ (joinPos z p))
    simpa only [Pos, Fintype.card_prod, Fintype.card_fin] using
      CanMake.iUnion (fun l => CanMake.range (entry l))
  let T := S ∪ ((⋃ l, Set.range (A l)) ∪ (⋃ l, Set.range (B l)))
  have prod (l : Fin r) : CanMake T cost (Set.range (mm (A l) (B l))) :=
    ih T (A l) (B l) (fun x => Or.inl (hS x))
      (fun p => Or.inr (Or.inl (Set.mem_iUnion_of_mem l ⟨p, rfl⟩)))
      (fun p => Or.inr (Or.inr (Set.mem_iUnion_of_mem l ⟨p, rfl⟩)))
  let U := T ∪ (⋃ l, Set.range (mm (A l) (B l)))
  have finish (u : Pos (i * d) (j * e)) : CanMake U (Fintype.card (Fin r) * 2) {mm X Y u} := by
    obtain ⟨z, p, rfl⟩ := joinPos_surj u
    rw [hc]
    exact CanMake.linear (Or.inl (Or.inl h0)) (fun l => Or.inl (Or.inl (hS (c l z))))
      (fun l => Or.inr (Set.mem_iUnion_of_mem l ⟨p, rfl⟩))
  have start := ((prep a X hX).union (prep b Y hY)).keep
  have whole := (start.trans (CanMake.iUnion prod).keep).trans (CanMake.range finish)
  refine whole.mono_cost ?_
  simp only [Pos, Fintype.card_prod, Fintype.card_fin]
  exact le_of_eq (by ring)

private def pad {i j : ℕ} (d e : ℕ) (X : Pos i j → K) (p : Pos (i + d) (j + e)) : K :=
  if h : p.1.val < i ∧ p.2.val < j then X (⟨p.1.val, h.1⟩, ⟨p.2.val, h.2⟩) else 0

private lemma multiplies_smaller {i j k u v w cost : ℕ} (hi : i ≤ u) (hj : j ≤ v) (hk : k ≤ w)
    (h : Multiplies F K u v w cost) : Multiplies F K i j k cost := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hj
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hk
  intro S X Y hS hX hY
  have hpad {m n a b : ℕ} (Z : Pos m n → K) (hZ : ∀ p, Z p ∈ S) (p : Pos (m + a) (n + b)) :
      pad a b Z p ∈ S := by
    unfold pad
    split
    · exact hZ _
    · simpa using hS 0
  refine (h S (pad d f X) (pad f e Y) hS (hpad X hX) (hpad Y hY)).mono_output ?_
  rintro _ ⟨⟨x, y⟩, rfl⟩
  refine ⟨(Fin.castAdd d x, Fin.castAdd e y), ?_⟩
  simp [mm, Fin.sum_univ_add, pad]

private def powerCost (i j k r : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => r * powerCost i j k r t + 2 * r * (i * j * (i * j) ^ t + i * k * (i * k) ^ t + j * k * (j * k) ^ t)

private lemma multiplies_power {i j k r : ℕ} (h : Integral.Rank F i j k r) (t : ℕ) :
    Multiplies F K (i ^ t) (j ^ t) (k ^ t) (powerCost i j k r t) := by
  induction t with
  | zero => simpa only [pow_zero, powerCost] using (multiplies_one (F := F) (K := K))
  | succ t ih => simpa only [powerCost, pow_succ', mul_pow] using multiplies_step h ih

/-- A rank witness gives a cost recurrence valid up to each power of the
block dimensions. The overhead grows with the largest of the three areas. -/
theorem integral_power_cost {i j k r : ℕ} (h : Integral.Rank F i j k r) :
    ∃ D : ℕ, ∃ a : ℕ → ℕ, (∀ t, a (t + 1) ≤ r * a t + D * (max (i * j) (max (i * k) (j * k))) ^ t) ∧
      ∀ t I J K : ℕ, I ≤ i ^ t → J ≤ j ^ t → K ≤ k ^ t → ∃ m, Integral.Computes F I J K m ∧ m ≤ a t := by
  refine ⟨2 * r * (i * j + i * k + j * k), powerCost i j k r, ?_, ?_⟩
  · intro t
    rw [powerCost, mul_assoc (2 * r), add_mul, add_mul]
    gcongr <;> omega
  · intro t I J K hI hJ hK
    have hmul := multiplies_smaller hI hJ hK (multiplies_power (K := Integral.Poly F I J K) h t)
    obtain ⟨m, hm, T, hT, hout⟩ :=
      hmul (Integral.initial F I J K) (fun p => Integral.input F (.inl p)) (fun p => Integral.input F (.inr p))
        (fun x => Or.inl ⟨x, rfl⟩) (fun p => Or.inr ⟨.inl p, rfl⟩)
        (fun p => Or.inr ⟨.inr p, rfl⟩)
    exact ⟨m, ⟨T, hT, fun p => hout ⟨p, rfl⟩⟩, hm⟩

theorem power_cost {F : Type*} [Field F] {i j k r : ℕ} (h : RankLE F i j k r) :
    ∃ D : ℕ, ∃ a : ℕ → ℕ, (∀ t, a (t + 1) ≤ r * a t + D * (max (i * j) (max (i * k) (j * k))) ^ t) ∧
      ∀ t I J K : ℕ, I ≤ i ^ t → J ≤ j ^ t → K ≤ k ^ t → ∃ m, Computes F I J K m ∧ m ≤ a t := by
  obtain ⟨D, a, hstep, hpad⟩ := integral_power_cost h
  refine ⟨D, a, hstep, fun t I J K hI hJ hK => ?_⟩
  obtain ⟨m, hm, hcost⟩ := hpad t I J K hI hJ hK
  exact ⟨m, hm.field (RingHom.id F), hcost⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle

namespace OAI.LinearAlgebra.MatrixExponent

theorem power_cost {F : Type*} [Field F] {n r : ℕ} (h : RankLE F n r) :
    ∃ D : ℕ, ∃ a : ℕ → ℕ, (∀ j, a (j + 1) ≤ r * a j + D * (n ^ j) ^ 2) ∧
      ∀ j m : ℕ, m ≤ n ^ j → ∃ t, Computes F m t ∧ t ≤ a j := by
  obtain ⟨D, a, hstep, hpad⟩ := Rectangle.power_cost h
  refine ⟨D, a, ?_, fun j m hm => hpad j m m m hm hm hm⟩
  simpa only [max_self, mul_pow, pow_two] using hstep

end OAI.LinearAlgebra.MatrixExponent
