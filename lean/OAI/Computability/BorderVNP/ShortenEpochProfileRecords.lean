import OAI.Computability.BorderVNP.ShortenEpochLocalRecords

/-! # Descriptor and expanded costs of a seed's histogram network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Finset
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K]

/-- Per-block bound for internal widths and individual table uses, including
the selector word and its histogram checks. -/
noncomputable def profilePayloadBound (e : PaidIdentity K D m) : ℕ :=
  2 * profileWidthBound e + ∑ i, Fintype.card (e.net i).Site

private theorem sum_recordCost {E : Type*} [Fintype E] (exp : Bool) (v : E → ℕ) :
    ∑ i, recordCost exp (v i) = Fintype.card E + if exp then ∑ i, v i else 0 := by
  cases exp <;> simp [recordCost, sum_add_distrib]

/-- Total number of internal descriptors and expanded costs of one actual seed
profile. External hooks will be charged to the old cable ends separately. -/
theorem seed_internal_records_le (e : PaidIdentity K D m) (exp : Bool) (j : ℕ)
    (q : Fin e.count → ℕ) (hq : ∑ i, q i = j) :
    (∑ v, recordCost exp (bankUses e j q v)) +
      2 * (∑ c, recordCost exp ((e.profile j q).width c)) ≤
    profileDescriptorBound e + (if exp then profilePayloadBound e * j else 0) := by
  rw [sum_recordCost, sum_recordCost]
  have he : (∑ c, (e.profile j q).width c) ≤ j * profileWidthBound e := by
    have ht (u : Fin D × Bool) : ‖antipodalPosition u‖ ≤ 1 := by rcases u with ⟨i,b⟩; cases b <;> simp [antipodalPosition]
    have hw := Profile.totalWidth e.net antipodalPosition ht j q hq
    change (∑ c, (Profile.network e.net antipodalPosition ht j q).width c) ≤ _
    rw [hw]
    have hqle (i : Fin e.count) : q i ≤ j :=
      (single_le_sum (f := q) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans_eq hq
    have hbank : (∑ i, q i * ∑ c, (e.net i).width c) ≤ j * ∑ i, ∑ c, (e.net i).width c := by
      rw [mul_sum]; exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hqle i)
    unfold profileWidthBound
    nlinarith only [hbank,Nat.zero_le (j*(2*D*m))]
  have hcardS : Fintype.card (e.profile j q).Site = Fintype.card (e.profile 0 (fun _ => 0)).Site := rfl
  have hcardE : Fintype.card (e.profile j q).Edge = Fintype.card (e.profile 0 (fun _ => 0)).Edge := rfl
  rw [hcardS,hcardE]
  cases exp with
  | false => simp [profileDescriptorBound]
  | true =>
    simp only [ite_true, profileDescriptorBound, profilePayloadBound]
    linarith only [he, sum_bankUses_le e j q hq]

/-- The retained old end of an inserted hook. -/
noncomputable def oldHookSite {P : Type*} {bits : P → ℕ} (N : Network D P bits) (S : Finset N.Edge)
    (k : N.CutPorts S) : N.Site := (N.cut S).attach (.inr k)

/-- Cost of all retained or exposed old ends at the given site test. -/
noncomputable def endRecords {P : Type*} {bits : P → ℕ} (N : Network D P bits) (exp : Bool)
    (test : N.Site → Prop) : ℕ :=
  testedWidth (fun c => recordCost exp (N.width c)) (fun c => test (N.src c)) +
  testedWidth (fun c => recordCost exp (N.width c)) (fun c => test (N.dst c))

/-- The old ends exposed as hooks form a subset of the old end records. -/
theorem hook_records_le {P : Type*} {bits : P → ℕ} (N : Network D P bits) (S : Finset N.Edge)
    (exp : Bool) (test : N.Site → Prop) :
    (∑ k : N.CutPorts S, if test (oldHookSite N S k) then recordCost exp (N.cutWidths S k) else 0) ≤
      endRecords N exp test := by
  classical
  have side (f : N.Edge → ℕ) : (∑ e : ↥S, f e.val) ≤ ∑ e, f e := by
    rw [Finset.sum_coe_sort]
    exact sum_le_sum_of_subset (subset_univ _)
  rw [Fintype.sum_sum_type (fun k : ↥S ⊕ ↥S =>
    if test (oldHookSite N S k) then recordCost exp (N.cutWidths S k) else 0)]
  exact Nat.add_le_add (side (fun c => if test (N.src c) then recordCost exp (N.width c) else 0))
    (side (fun c => if test (N.dst c) then recordCost exp (N.width c) else 0))

end Shortening

end BorderVNP
end Computability
end OAI
