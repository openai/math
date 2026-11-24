import OAI.Computability.VPVNP.PairSimulationEntryWork
import OAI.Computability.VPVNP.CompressionHistory

/-!
# Summing local map checks and leaf runs in a placement history

Each selected term places old vertices intact at one output vertex. The
work of its map interpreters and of the original leaves therefore obeys
the same placement-fiber recurrence as the recorded occurrence count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel Compression

variable {k A : Type*} [Field k] {S : BlockSchedule k} {N Y : Network}

/-- Interpreter inputs at the individual map slots of an entire branch.
The index on each invocation is the degree recorded at that slot. -/
def MapInputs (B : S.Templates) : {N Y : Network} → TermChain A N Y → Type
  | _, _, .done _ => PUnit
  | _, _, .more _ rec tail =>
    (∀ v i, MapInvocation B ((rec v).degree i)) × MapInputs B tail

open scoped Classical in
/-- Sum the instruction charges of individual recorded map slots and original leaves
inside the actual preimage subtree of each final site. -/
noncomputable def mapAndLeafCost {B : S.Templates}
    (cost : {d : ℕ} → MapInvocation B d → ℕ) : {N Y : Network} → (c : TermChain A N Y) →
    MapInputs B c → (N.Site → ℕ) → Y.Site → ℕ
  | _, _, .done _, _, leaf => leaf
  | _, _, .more t _ tail, calls, leaf =>
    mapAndLeafCost cost tail calls.2 fun v ↦
      (∑ i, cost (calls.1 v i)) + ∑ u : t.Preimage v, leaf u.val

/-- Metered interpreter charges in the same placement fibers. -/
noncomputable abbrev mapAndLeafWork {B : S.Templates} (c : TermChain A N Y) (calls : MapInputs B c)
    (leaf : N.Site → ℕ) := mapAndLeafCost MapInvocation.work c calls leaf

/-- This bound holds for every input to every recorded interpreter, without
an acceptance requirement or equality of independently supplied half-wires. -/
theorem mapAndLeafCost_le {B : S.Templates} (cost : {d : ℕ} → MapInvocation B d → ℕ)
    (c : TermChain A N Y) (calls : MapInputs B c)
    {L T : ℕ} (hk : ∀ d ≤ L, ∀ m : MapInvocation B d, cost m ≤ T)
    (hl : c.AllRecordsLe L) (leaf count : N.Site → ℕ)
    (hstart : ∀ v, leaf v ≤ count v * T) :
    ∀ v, mapAndLeafCost cost c calls leaf v ≤ c.occurrences count v * T := by
  classical
  induction c with
  | done => exact hstart
  | more t rec tail ih =>
    apply ih calls.2 hl.2.2 _ (t.pushHistorySize rec count)
    intro v
    rw [Term.pushHistorySize, Nat.add_mul, Finset.sum_mul]
    apply Nat.add_le_add
    · calc
        _ ≤ ∑ _i : (rec v).Map, T := Finset.sum_le_sum fun i _ ↦
          hk _ (hl.2.1 v i) (calls.1 v i)
        _ = Fintype.card (rec v).Map * T := by simp
        _ ≤ (rec v).count * T :=
          Nat.mul_le_mul_right _ (by unfold SiteRecords.count; omega)
    · exact Finset.sum_le_sum fun u _ ↦ hstart u.val

/-- This bound holds for every input to every recorded interpreter, without
an acceptance requirement or equality of independently supplied half-wires. -/
theorem mapAndLeafWork_le {B : S.Templates} (c : TermChain A N Y) (calls : MapInputs B c)
    {K L T : ℕ} (hk : ∀ d (m : MapInvocation B d), m.work ≤ K * (d + 1) ^ 2)
    (hl : c.AllRecordsLe L) (ht : K * (L + 1) ^ 2 ≤ T) (leaf count : N.Site → ℕ)
    (hstart : ∀ v, leaf v ≤ count v * T) :
    ∀ v, mapAndLeafWork c calls leaf v ≤ c.occurrences count v * T := by
  apply mapAndLeafCost_le MapInvocation.work c calls _ hl leaf count hstart
  intro d hd m
  exact (hk d m).trans ((Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.succ_le_succ hd) 2)).trans ht)

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
