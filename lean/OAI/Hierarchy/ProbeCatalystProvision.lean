import OAI.Hierarchy.ProbeIntegerBatch
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI
/-! # Funding every actual catalyst occurrence at its physical site -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

/-- Native selected positive demands debit J*b bits. The runtime may use the
uniform common J shared by all packets in the finite catalogue. -/
theorem catalyst_bits_le {w K b J : ℕ} (hK : 0<K) (copies : J≤copied K b w) : J*b≤w := by
  have many := (Nat.mul_le_mul_right (K*b) copies).trans (Nat.div_mul_le_self w (K*b))
  have bcap : b≤K*b := by simpa using Nat.mul_le_mul_right b hK
  exact (Nat.mul_le_mul_left J bcap).trans many

/-- The actual per-axis debits of one overlap-free strip collection. `slot` is
`payloadPlaceAll` or `allStripColumns`, restricted to the admitted failure rows. -/
def catalystDebit {V C : Type*} [Fintype V] (slot : V↪C) (bits : V→ℕ) (c : C) :=
  ∑ v, if slot v=c then bits v else 0

theorem catalyst_debit_le {V C : Type*} [Fintype V] (slot : V↪C) (bits : V→ℕ)
    (c : C) (w : ℕ) (bound : ∀v,bits v≤w) : catalystDebit slot bits c≤w := by
  classical
  by_cases used : ∃v,slot v=c
  · obtain ⟨v,rfl⟩ := used
    simpa [catalystDebit,Function.Embedding.apply_eq_iff_eq] using bound v
  · have none (v : V) : slot v≠c := fun eq => used ⟨v,eq⟩
    simp [catalystDebit,none]

/-- Uses through a real chronological prefix. Each event can have a different
set of selected packets, number of columns and physical placement. -/
def catalystSpent {T C : Type*} [DecidableEq T] (rows : T→Type*) [∀t,Fintype (rows t)]
    (slot : ∀t,rows t↪C) (bits : ∀t,rows t→ℕ) (events : Finset T) (c : C) : ℕ :=
  ∑ t∈events, catalystDebit (slot t) (bits t) c

theorem catalyst_funded {T C : Type*} [DecidableEq T] [Fintype C] (rows : T→Type*)
    [∀t,Fintype (rows t)] (slot : ∀t,rows t↪C) (bits : ∀t,rows t→ℕ) (events : Finset T)
    {fuel w : ℕ} (clock : events.card≤fuel) (per : ∀t∈events,∀v,bits t v≤w) :
    let spent := catalystSpent rows slot bits events
    (∀ c,spent c≤fuel*w) ∧
    (∑c,spent c) + (∑c,(fuel*w-spent c))=Fintype.card C*(fuel*w) := by
  classical
  intro spent
  have one (c : C) : spent c≤fuel*w := calc
    _ ≤ ∑ _∈events,w := Finset.sum_le_sum fun t hit => catalyst_debit_le (slot t) (bits t) c w (per t hit)
    _ = events.card*w := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ clock
  refine ⟨one,?_⟩
  rw [← Finset.sum_add_distrib]
  simp [Nat.add_sub_of_le (one _)]

end
end Hierarchy.AdaptiveProbe

end OAI
