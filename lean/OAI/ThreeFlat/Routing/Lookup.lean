import OAI.LinearAlgebra.SpectralBooks.BatchedLookup
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

namespace OAI
/-!
# Batched lookup by one tagged switch

The switch carries each record together with its original position. At its
output, adjacent records are checked in lexicographic order by (key, position).
There is a unique setting of all the guessed tags and output fields that passes
these tests, including when many requests have identical keys and values.
-/

namespace ThreeFlat.Routing

open scoped BigOperators Classical
open LinearAlgebra.SpectralBooks

/-- The transported data agree at each tagged destination, and all destinations
are hit exactly once. -/
def Routed {I X : Type*} (tag : I → I) (input output : I → X) : Prop :=
  Function.Bijective tag ∧ ∀ i, output (tag i) = input i

/-- The tensor checked by a tagged-permutation network. -/
noncomputable def taggedSwitch (K : Type*) [Zero K] [One K] {I X : Type*}
    (tag : I → I) (input output : I → X) : K := by
  classical exact if Routed tag input output then 1 else 0

/-- One strict lexicographic comparison for each pair of consecutive positions. -/
def AdjacentIncreasing {n : ℕ} {A : Type*} [Preorder A] (x : Fin n → A) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → x i < x j

private theorem adjacentIncreasing_iff {n : ℕ} {A : Type*} [Preorder A]
    (x : Fin n → A) : AdjacentIncreasing x ↔ StrictMono x := by
  constructor
  · intro h
    cases n with
    | zero => exact fun i => Fin.elim0 i
    | succ n => exact Fin.strictMono_iff_lt_succ.mpr fun i => h i.castSucc i.succ rfl
  · intro h i j hj
    exact h (show i < j from Nat.lt_of_succ_le hj.le)

/-- Conditions tested by the tagged switch and the adjacent comparisons on its
output. The source index resolves all ties. -/
def StableRouting {n : ℕ} {A X : Type*} [LinearOrder A] (key : X → A)
    (input : Fin n → X) (tag source : Fin n → Fin n) (output : Fin n → X) : Prop :=
  Routed tag (fun i => (i, input i)) (fun j => (source j, output j)) ∧
    AdjacentIncreasing (fun j => toLex (key (output j), source j))

theorem stableRouting_iff {n : ℕ} {A X : Type*} [LinearOrder A] (key : X → A)
    (input : Fin n → X) (tag source : Fin n → Fin n) (output : Fin n → X) :
    let σ := Tuple.sort (key ∘ input)
    StableRouting key input tag source output ↔
      tag = (σ.symm : Fin n → Fin n) ∧ source = (σ : Fin n → Fin n) ∧ output = input ∘ σ := by
  classical
  dsimp only
  let σ := Tuple.sort (key ∘ input)
  constructor
  · rintro ⟨⟨bij, routed⟩, adjacent⟩
    let e : Equiv.Perm (Fin n) := Equiv.ofBijective tag bij
    have at_dest j : (source j, output j) = (e.symm j, input (e.symm j)) := by
      have H := routed (e.symm j)
      change (source (e (e.symm j)), output (e (e.symm j))) = _ at H
      simpa using H
    have src : source = (e.symm : Fin n → Fin n) := funext fun j => congrArg Prod.fst (at_dest j)
    have out : output = input ∘ e.symm := funext fun j => congrArg Prod.snd (at_dest j)
    have he : e.symm = σ := by
      apply Tuple.eq_sort_iff'.2
      rw [src, out] at adjacent
      exact (adjacentIncreasing_iff _).mp adjacent
    refine ⟨?_, src.trans (congrArg DFunLike.coe he), ?_⟩
    · change (e : Fin n → Fin n) = (σ.symm : Fin n → Fin n)
      rw [← he]
      rfl
    · rw [out, he]
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨⟨σ.symm.bijective, ?_⟩, (adjacentIncreasing_iff _).mpr ?_⟩
    · intro i
      simp [Function.comp_apply]
    · exact Tuple.eq_sort_iff'.mp (rfl : σ = Tuple.sort (key ∘ input))

/-- Summing all destination guesses, original-position fields and payload fields
with the local checks leaves a single copy of the sorted contribution. -/
theorem taggedSwitch_sort_contract {K A X : Type*} [Semiring K] [LinearOrder A] [Fintype X]
    {n : ℕ} (key : X → A) (input : Fin n → X) (score : (Fin n → X) → K) :
    let σ := Tuple.sort (key ∘ input)
    (∑ tag : Fin n → Fin n, ∑ source : Fin n → Fin n, ∑ output : Fin n → X,
      taggedSwitch K tag (fun i => (i, input i)) (fun j => (source j, output j)) *
        (if AdjacentIncreasing (fun j => toLex (key (output j), source j))
          then score output else 0)) = score (input ∘ σ) := by
  classical
  dsimp only
  let σ := Tuple.sort (key ∘ input)
  have term (tag source : Fin n → Fin n) (output : Fin n → X) :
      taggedSwitch K tag (fun i => (i, input i)) (fun j => (source j, output j)) *
        (if AdjacentIncreasing (fun j => toLex (key (output j), source j))
          then score output else 0) =
        if tag = (σ.symm : Fin n → Fin n) ∧ source = (σ : Fin n → Fin n) ∧
          output = input ∘ σ then score output else 0 := by
    have iff' : StableRouting key input tag source output ↔
        tag = (σ.symm : Fin n → Fin n) ∧ source = (σ : Fin n → Fin n) ∧
        output = input ∘ σ := stableRouting_iff key input tag source output
    simp only [← iff']
    unfold taggedSwitch StableRouting
    split_ifs <;> simp_all
  simp_rw [term, ite_and]
  simp [σ]

/-- Use the transported lookup records in the table-before-request scan. The
contribution is the product of the original requests' weights at their true
answers, in every characteristic. -/
theorem batchedLookup_contract {K V T X : Type*} [CommSemiring K] [Fintype X]
    {n : ℕ} (record : X → LookupRecord V T) (input : Fin n → X) (table : ℕ → Option V)
    (weight : T × Option V → K)
    (rows : ∀ k v, LookupRecord.row k v ∈ List.ofFn (record ∘ input) → table k = some v)
    (covers : ∀ k t v, LookupRecord.request k t ∈ List.ofFn (record ∘ input) →
      table k = some v → LookupRecord.row k v ∈ List.ofFn (record ∘ input)) :
    (∑ tag : Fin n → Fin n, ∑ source : Fin n → Fin n, ∑ output : Fin n → X,
      taggedSwitch K tag (fun i => (i, input i)) (fun j => (source j, output j)) *
        (if AdjacentIncreasing (fun j => toLex ((record (output j)).key, source j))
          then (((LookupRecord.scan none (List.ofFn (record ∘ output))).map weight).prod)
          else 0)) =
        ((LookupRecord.answers table (List.ofFn (record ∘ input))).map weight).prod := by
  classical
  let key : X → ℕ := fun a => (record a).key
  let σ := Tuple.sort (key ∘ input)
  rw [taggedSwitch_sort_contract key input
    (fun output => ((LookupRecord.scan none (List.ofFn (record ∘ output))).map weight).prod)]
  have hp := σ.ofFn_comp_perm (record ∘ input)
  have hsorted : (List.ofFn ((record ∘ input) ∘ σ)).Pairwise
      (fun a b => a.key ≤ b.key) :=
    List.pairwise_ofFn.mpr fun _ _ hij => Tuple.monotone_sort (key ∘ input) hij.le
  exact ((LookupRecord.scan_sorted_perm table hp hsorted rows covers).map weight).prod_eq

end ThreeFlat.Routing

end OAI
