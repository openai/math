import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm

/-!
# Extracting squarefree coefficients of parse products

In §8.1 of *VP and VNP differ over every field*, each queried monomial uses each
of its variables once. A product gate partitions those variables between its two
ordered children. For a product of linear forms this amounts to assigning each
leaf one queried variable, using every queried variable exactly once.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {σ ι κ R : Type*} [CommSemiring R]

/-- The exponent vector of the squarefree monomial supported on `s`. -/
noncomputable def squarefreeDegree (s : Finset σ) : σ →₀ ℕ :=
  ∑ j ∈ s, Finsupp.single j 1

@[simp] theorem squarefreeDegree_apply [DecidableEq σ] (s : Finset σ) (j : σ) :
    squarefreeDegree s j = if j ∈ s then 1 else 0 := by
  simp [squarefreeDegree, Finsupp.finsetSum_apply, Finsupp.single_apply]

@[simp] theorem support_squarefreeDegree (s : Finset σ) : (squarefreeDegree s).support = s := by
  classical
  ext j
  by_cases hj : j ∈ s <;> simp [Finsupp.mem_support_iff, hj]

private theorem split_squarefreeDegree [DecidableEq σ] {s : Finset σ} {a b : σ →₀ ℕ}
    (h : a + b = squarefreeDegree s) :
    a.support ⊆ s ∧ squarefreeDegree a.support = a ∧ squarefreeDegree (s \ a.support) = b := by
  have hj (j : σ) : a j + b j = if j ∈ s then 1 else 0 := by
    simpa using DFunLike.congr_fun h j
  refine ⟨?_, Finsupp.ext fun j ↦ ?_, Finsupp.ext fun j ↦ ?_⟩
  · intro j hj'
    have hnon := Finsupp.mem_support_iff.mp hj'
    by_contra hjs
    simpa [hjs, hnon] using hj j
  · simp only [squarefreeDegree_apply, Finsupp.mem_support_iff]
    have := hj j
    split at this <;> split <;> omega
  · simp only [squarefreeDegree_apply, Finset.mem_sdiff, Finsupp.mem_support_iff]
    have := hj j
    by_cases hjs : j ∈ s <;> simp [hjs] at this ⊢ <;> (try split_ifs) <;> omega

/-- The coefficient at a squarefree monomial of a product is a sum over subsets.
The first factor uses exactly that subset and the second factor uses its complement. -/
theorem coeff_mul_squarefree [DecidableEq σ] (p q : MvPolynomial σ R) (s : Finset σ) :
    (p * q).coeff (squarefreeDegree s) =
      ∑ t ∈ s.powerset, p.coeff (squarefreeDegree t) * q.coeff (squarefreeDegree (s \ t)) := by
  rw [coeff_mul]
  symm
  refine Finset.sum_bij (fun t _ ↦ (squarefreeDegree t, squarefreeDegree (s \ t)))
    ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro t ht
    apply Finset.mem_antidiagonal.mpr
    apply Finsupp.ext
    intro j
    by_cases hjt : j ∈ t
    · simp [hjt, Finset.mem_powerset.mp ht hjt]
    · simp [hjt]
  · intro t _ u _ h
    simpa using congrArg (fun x : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ x.1.support) h
  · rintro ⟨a,b⟩ h
    obtain ⟨hsub, ha, hb⟩ := split_squarefreeDegree (Finset.mem_antidiagonal.mp h)
    exact ⟨a.support, Finset.mem_powerset.mpr hsub, Prod.ext ha hb⟩

private theorem assignment_degree_eq_iff [Fintype ι] (s : Finset σ) (f : ι → σ) :
    (∑ i, Finsupp.single (f i) 1) = squarefreeDegree s ↔
      ∃ e : ι ≃ ↥s, ∀ i, (e i : σ) = f i := by
  classical
  constructor
  · intro h
    have hcount (j : σ) :
        (Finset.univ.filter (fun i ↦ f i = j)).card = if j ∈ s then 1 else 0 := by
      have hj := DFunLike.congr_fun h j
      simpa [squarefreeDegree_apply, Finsupp.finsetSum_apply, Finsupp.single_apply] using hj
    have hmem (i : ι) : f i ∈ s := by
      by_contra hnot
      have hzero : (Finset.univ.filter (fun k ↦ f k = f i)).card = 0 := by
        simpa [hnot] using hcount (f i)
      have hempty := Finset.card_eq_zero.mp hzero
      have hi : i ∈ Finset.univ.filter (fun k ↦ f k = f i) := by simp
      simp [hempty] at hi
    have hone (j : ↥s) : ∃! i, f i = j.val := by
      have hc : (Finset.univ.filter (fun i ↦ f i = j.val)).card = 1 := by
        simpa [j.property] using hcount j.val
      simpa using Finset.card_eq_one_iff_existsUnique.mp hc
    let g (i : ι) : ↥s := ⟨f i, hmem i⟩
    have hb : Function.Bijective g := by
      constructor
      · intro a b hab
        exact (hone (g b)).unique (congrArg Subtype.val hab) rfl
      · intro j
        obtain ⟨i, hi⟩ := (hone j).exists
        exact ⟨i, Subtype.ext hi⟩
    exact ⟨Equiv.ofBijective g hb, fun _ ↦ rfl⟩
  · rintro ⟨e, he⟩
    simp_rw [← he]
    calc
      ∑ i, Finsupp.single ((e i).val) 1 =
          ∑ j : ↥s, Finsupp.single j.val 1 :=
        e.sum_comp (fun j ↦ Finsupp.single j.val (1 : ℕ))
      _ = squarefreeDegree s := by
        simpa only [squarefreeDegree, Finset.attach_eq_univ] using
          Finset.sum_attach s (fun j ↦ Finsupp.single j (1 : ℕ))

/-- A squarefree coefficient of a product of linear forms is the sum of the
weights of all bijections from the factors to the selected variables. -/
theorem coeff_prod_linearForms [Fintype σ] [Fintype ι] [DecidableEq σ] [DecidableEq ι]
    (s : Finset σ) (a : ι → σ → R) :
    (∏ i, ∑ j, C (a i j) * X j).coeff (squarefreeDegree s) =
      ∑ e : ι ≃ ↥s, ∏ i, a i (e i).val := by
  classical
  simp_rw [C_mul_X_eq_monomial]
  rw [Fintype.prod_sum, coeff_sum]
  simp_rw [← monomial_sum_prod, coeff_monomial]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun (e : ι ≃ ↥s) _ ↦ fun i ↦ (e i).val)
  · intro e _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (assignment_degree_eq_iff _ _).mpr
      ⟨e, fun _ ↦ rfl⟩⟩
  · intro e _ e' _ h
    exact Equiv.ext fun i ↦ Subtype.ext (congrFun h i)
  · intro f hf
    obtain ⟨e, he⟩ := (assignment_degree_eq_iff s f).mp (Finset.mem_filter.mp hf).2
    exact ⟨e, Finset.mem_univ _, funext he⟩
  · intro _ _
    rfl

/-- Indexed form of the leaf-bijection rule in §8.1. The query is an embedding,
so every chosen variable occurs once even when a leaf could choose any variable
of the ambient polynomial ring. -/
theorem coeff_prod_linearForms_query [Fintype σ] [Fintype ι] [Fintype κ]
    [DecidableEq σ] [DecidableEq ι] [DecidableEq κ] (query : κ ↪ σ) (a : ι → σ → R) :
    (∏ i, ∑ j, C (a i j) * X j).coeff (∑ j, Finsupp.single (query j) 1) =
      ∑ e : ι ≃ κ, ∏ i, a i (query (e i)) := by
  let s := Finset.univ.map query
  have hd : squarefreeDegree s = ∑ j, Finsupp.single (query j) 1 := by
    simp [s, squarefreeDegree]
  rw [← hd, coeff_prod_linearForms]
  let u : κ ≃ ↥(Finset.univ : Finset κ) :=
    ⟨fun j ↦ ⟨j, Finset.mem_univ j⟩, Subtype.val, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let e := u.trans (Finset.equivMap query Finset.univ)
  exact ((Equiv.equivCongr (Equiv.refl ι) e).sum_comp
    (fun f : ι ≃ ↥s ↦ ∏ i, a i (f i).val)).symm

end VPVNP
end Computability
end OAI
