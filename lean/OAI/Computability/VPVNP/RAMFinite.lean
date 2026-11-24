import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Data.Set.Finite.List
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.DeriveFintype

/-!
# Finite path counts for burst RAMs

The fuel bound makes the event history of an individual call finite. The
charge for starting a call also bounds the number of calls in an accepting
execution. These two bounds suffice even when the set of private machine
configurations is infinite. Fixing all shared bits leaves an independent
choice of a valid report list at each site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

deriving instance Fintype for Event

/-- A report list with boundedly many calls, each of which fits its instruction fuel. -/
abbrev BoundedReports (w fuel maxCalls : ℕ) :=
  {rs : List (Report w) // rs.length ≤ maxCalls ∧ ∀ r ∈ rs, r.events.length < fuel}

private theorem finite_shortReports (w fuel : ℕ) :
    Finite {r : Report w // r.events.length < fuel} := by
  let : Finite {es : List (Event w) // es.length < fuel} := List.finite_length_lt _ _
  let encode (r : {r : Report w // r.events.length < fuel}) :
      {es : List (Event w) // es.length < fuel} × Option (Word w) :=
    (⟨r.val.events, r.property⟩, r.val.result)
  apply Finite.of_injective encode
  rintro ⟨⟨es, s⟩, _⟩ ⟨⟨fs, t⟩, _⟩ h
  simpa [encode] using h

instance (w fuel maxCalls : ℕ) : Finite (BoundedReports w fuel maxCalls) := by
  let Short := {r : Report w // r.events.length < fuel}
  let : Finite Short := finite_shortReports w fuel
  let : Finite {rs : List Short // rs.length ≤ maxCalls} := List.finite_length_le _ _
  let encode (rs : BoundedReports w fuel maxCalls) : {rs : List Short // rs.length ≤ maxCalls} :=
    ⟨rs.val.attachWith _ rs.property.2, List.length_attachWith.le.trans rs.property.1⟩
  apply Finite.of_injective encode
  intro rs ts he
  apply Subtype.ext
  simpa [encode, Short] using congrArg (fun xs => xs.val.map (Subtype.val : Short → Report w)) he

/-- Every locally replayed call obeys its own instruction bound. -/
theorem localSegment_event_bound {P : Program w C} {fuel s rs}
    (h : LocalSegment P fuel s rs) : ∀ r ∈ rs, r.events.length < fuel := by
  induction rs generalizing s with
  | nil => simp
  | cons a rs ih =>
    cases s with
    | none => contradiction
    | some s =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hmem
      · exact h.1.length_lt
      · exact ih h.2 _ hmem

/-- The cost cap bounds the total number of calls, including calls without probes. -/
theorem boundedReports_of_localSegment {P : Program w C} {fuel maxCalls s rs}
    (h : LocalSegment P fuel s rs) (hc : RAMBuckets.cost Report.probes rs ≤ maxCalls) :
    rs.length ≤ maxCalls ∧ ∀ r ∈ rs, r.events.length < fuel := by
  rw [RAMBuckets.cost_eq_length_add_probes] at hc
  exact ⟨by omega, localSegment_event_bound h⟩

theorem finite_verifiedReports {P : Program w C} {fuel initial m withinCaps maxCalls}
    (hcap : ∀ rs, withinCaps rs → RAMBuckets.cost Report.probes rs ≤ maxCalls) :
    Finite (VerifiedReports P fuel initial m withinCaps) := by
  let encode (r : VerifiedReports P fuel initial m withinCaps) : BoundedReports w fuel maxCalls :=
    ⟨r.val, boundedReports_of_localSegment r.property.1 (hcap _ r.property.2.2.2)⟩
  exact Finite.of_injective encode fun _ _ he => Subtype.ext (congrArg (fun t : BoundedReports w fuel maxCalls => t.val) he)

theorem finite_actualPaths {P : Program w C} {fuel initial m withinCaps maxCalls}
    (hcap : ∀ rs, withinCaps rs → RAMBuckets.cost Report.probes rs ≤ maxCalls) :
    Finite (ActualPaths P fuel initial m withinCaps) := by
  let := finite_verifiedReports (P := P) (fuel := fuel) (initial := initial) (m := m) hcap
  exact Finite.of_equiv _ (reportEquiv P fuel initial m withinCaps).symm

/-- Pairing a shared assignment with separate local witnesses enforces precisely
all the local checks on the pair. -/
def siteWitnessEquiv {Shared Site : Type*} {Local : Site → Type*}
    (valid : Shared → (i : Site) → Local i → Prop) :
    {t : Shared × ((i : Site) → Local i) // ∀ i, valid t.1 i (t.2 i)} ≃
      ((b : Shared) × ((i : Site) → {r : Local i // valid b i r})) where
  toFun t := ⟨t.val.1, fun i => ⟨t.val.2 i, t.property i⟩⟩
  invFun t := ⟨⟨t.1, fun i => (t.2 i).val⟩, fun i => (t.2 i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Counting independent local witnesses after fixing the shared assignment
turns the number of transcripts into a sum of products. -/
theorem card_siteWitnesses {Shared Site : Type*} [Fintype Shared] [Fintype Site]
    {Local : Site → Type*} [∀ i, Finite (Local i)] (valid : Shared → (i : Site) → Local i → Prop) :
    Nat.card {t : Shared × ((i : Site) → Local i) // ∀ i, valid t.1 i (t.2 i)} =
      ∑ b, ∏ i, Nat.card {r : Local i // valid b i r} := by
  rw [Nat.card_congr (siteWitnessEquiv valid), Nat.card_sigma]
  simp only [Nat.card_pi]

end BurstRAM

end VPVNP
end Computability
end OAI
