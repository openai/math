import OAI.Computability.BorderVNP.ShortenEpochSewnRecords
import OAI.Computability.BorderVNP.ShortenCombiningConcentration

/-!
# Uniform local size of a physical combining step

Each donor bin is counted at most once. In expanded mode its entire width
can be paid by the cable-end data of a bounded neighborhood. Public mode
pays once per nearby seed, even if no blocks were matched at that seed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.CombiningStep

open Crossing Epoch SeedIntervals Finset
open scoped Classical

variable {D m : ℕ} [NeZero D] {P : Type*} [Fintype P] {bits : P → ℕ}
variable {K : Type*} [Field K] {A : Type} [Fintype A]
variable (p : Pack D P bits K) (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)

omit [Field K] [Fintype A] in
/-- Expanded costs of all matched blocks at the nearby seeds are paid by old
source-end records in the input neighborhood. -/
theorem nearby_blocks_le (hm : 0 < m) (prior payload : p.layout.Site → ℕ)
    (near : Finset A) (region : p.layout.Site → Prop)
    (hdonor : ∀ c a, a ∈ near → bin c = some (perm 0 a) → region (p.layout.src c)) :
    ∑ a ∈ near, blocks p.layout bin perm m a ≤ localRecords p.layout true prior payload region := by
  classical
  have hp (c : p.layout.Edge) : (∑ a ∈ near, if bin c = some (perm 0 a) then p.layout.width c else 0) ≤
      if region (p.layout.src c) then recordCost true (p.layout.width c) else 0 := by
    by_cases ex : ∃ a ∈ near, bin c = some (perm 0 a)
    · obtain ⟨a,ha,hc⟩ := ex
      have eq (b : A) : (bin c = some (perm 0 b)) ↔ b = a := by rw [hc]; simp [eq_comm]
      simp [eq,ha,hdonor c a ha hc,recordCost]
    · have hn (a) (ha : a ∈ near) : bin c ≠ some (perm 0 a) := fun he => ex ⟨a,ha,he⟩
      rw [sum_eq_zero (fun a ha => ite_eq_right (hn a ha))]; exact Nat.zero_le _
  have hsum : (∑ a ∈ near, count p.layout bin (perm 0 a)) ≤
      testedWidth (fun c => recordCost true (p.layout.width c)) (fun c => region (p.layout.src c)) := by
    simp_rw [count_eq_sum]
    rw [sum_comm]
    exact sum_le_sum fun c _ => hp c
  have h := (sum_le_sum (s := near) (fun a _ => blocks_le_donor p bin perm hm a)).trans hsum
  unfold localRecords
  omega

set_option maxHeartbeats 1000000 in
/-- Per-tile descriptor or expanded cost of the actual sorted, matched and sewn
pack. Both neighborhood cardinalities are independent of the old tile load,
histogram, and quotient depth. -/
theorem physical_records_le {T : Type*} (e : PaidIdentity K D m) (hm : 0 < m)
    (positive : p.layout.Edge → Bool) (q : Counts e p bin perm)
    (expanded : Bool) (prior payload : p.layout.Site → ℕ) (tile : p.layout.Site → T)
    (tiles : Finset T) (near : Finset A) (post : (physical p bin perm e positive q).Site → Prop)
    (M U V : ℕ) (hcap : ∀ o, localRecords p.layout expanded prior payload (fun v => tile v = o) ≤ M)
    (hu : tiles.card ≤ U) (hv : near.card ≤ V)
    (hold : ∀ v, post (.inl v) → tile v ∈ tiles)
    (hhook : ∀ k, post (.inr (((partition p.layout bin perm m).parallel
      (seedNetwork e _ (p := pieces (m := m) p bin perm) _ (bundle p.layout bin perm m positive) q)).attach k)) →
      tile (oldHookSite (layout p.layout bin perm m) _ k) ∈ tiles)
    (hnew : ∀ a v, post (.inr ⟨a,v⟩) → a ∈ near)
    (hdonor : ∀ c a, a ∈ near → bin c = some (perm 0 a) → tile (p.layout.src c) ∈ tiles) :
    let t := partition p.layout bin perm m
    let b := bundle p.layout bin perm m positive
    let j := blocks p.layout bin perm m
    1 + localRecords (physical p bin perm e positive q) expanded
      (sewnPrior e j (p := pieces (m := m) p bin perm) t b q prior) (sewnPayload e j (p := pieces (m := m) p bin perm) t b q payload) post ≤
      (1 + (3 * Fintype.card (Band D) + profilePayloadBound e) * U +
        V * profileDescriptorBound e) * (1 + M) := by
  classical
  let t := partition p.layout bin perm m
  let b := bundle p.layout bin perm m positive
  let j := blocks p.layout bin perm m
  let region (v : p.layout.Site) := tile v ∈ tiles
  let C := Fintype.card (Band D)
  have hreg : localRecords p.layout expanded prior payload region ≤ U * M := by
    rw [localRecords_near]
    exact (sum_le_sum (s := tiles) (fun o _ => hcap o)).trans (by simpa using Nat.mul_le_mul_right M hu)
  have hband := (bands_localRecords p.layout (label p.layout bin perm m) expanded prior payload region).trans
    (Nat.mul_le_mul_left C hreg)
  have hfixed : (∑ _a ∈ near, profileDescriptorBound e) ≤ V * profileDescriptorBound e := by
    simpa using Nat.mul_le_mul_right (profileDescriptorBound e) hv
  have huse : (∑ a ∈ near, if expanded then profilePayloadBound e * j a else 0) ≤
      profilePayloadBound e * (U * M) := by
    cases expanded with
    | false => simp
    | true =>
      have h := (nearby_blocks_le p bin perm hm prior payload near region hdonor).trans hreg
      simpa only [ite_true, ← mul_sum] using Nat.mul_le_mul_left (profilePayloadBound e) h
  have hs := sewnProfile_records_le e j (p := pieces (m := m) p bin perm) t b q expanded prior payload
    region near post hold hhook hnew
  rw [sum_add_distrib] at hs
  change localRecords (pieces (m := m) p bin perm).layout expanded prior payload region ≤ C * (U*M) at hband
  change 1 + localRecords (physical p bin perm e positive q) expanded _ _ post ≤
    (1 + (3*C + profilePayloadBound e)*U + V * profileDescriptorBound e)*(1+M)
  linarith only [hs,hband,hfixed,huse,Nat.zero_le M,Nat.zero_le ((3*C+profilePayloadBound e)*U),
    Nat.zero_le (V*profileDescriptorBound e*M)]

end Shortening.CombiningStep

end BorderVNP
end Computability
end OAI
