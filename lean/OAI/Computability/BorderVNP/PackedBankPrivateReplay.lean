import OAI.Computability.BorderVNP.PackedHistoryPrivateSites
import OAI.Computability.BorderVNP.PackedBankRoundSchema

/-! # Induction on the original private-program replay

The property at a node is checked on its true normalized semantic state and
its actual saved private tapes. The base hypotheses are imposed independently
on each original leaf. No second enumeration of profiles or states is used.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Epoch.Round Diagonal.CellEntries Diagonal.ExternalSew
open scoped Classical
attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {I P K : Type} [Fintype I] [Fintype P] [Field K]
  {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
  (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

variable (good : ∀ n (x : A n), Site.Programs (view n x).pack.layout → Prop)

/-- Restriction of the actual initial parallel bank to one group of its leaves,
including the physical incidence-width identification. -/
noncomputable def subInitial (n : ℕ) (a : Leaves k (A 0) (n+1))
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) (n+1) a).layout) (j : Fin k) :
    Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n (a j)).layout :=
  let children := fun j : Fin k => (parallelLeaves (fun x => (view 0 x).pack) n (a j)).layout
  fun v => (initial ⟨j,v⟩).castWidth ((incoming_instances _ _).trans (Inherited.Parallel.incoming_eq children j v))

/-- Base condition on the original leaves of the supplied parallel tape. -/
def LeavesWithin : (n : ℕ) → (a : Leaves k (A 0) n) →
    Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout → Prop
  | 0, a, initial => good 0 a (fun v => (initial v).castWidth (incoming_instances _ _))
  | n+1, a, initial => ∀ j, LeavesWithin n (a j) (subInitial (view := view) n a initial j)

set_option maxHeartbeats 1200000 in
/-- Induction through the literal existing replay. Each step uses the saved
programs of its selected children and its attained profile ordinal. -/
theorem replayPrivatePrograms_invariant
    (step : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
      (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout),
      (∀ j, good i.val (c j) (old j)) →
      good (i.val+1) (F.advance i c q) (F.savePrivatePrograms store rows number i c q old))
    (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout)
    (hleaf : LeavesWithin (view := view) good n a initial) (q : (F.system.histories n hn a).Index) :
    good n (RowTrace.state F.system n hn a q) (F.replayPrivatePrograms store rows number n hn a initial q) := by
  induction n with
  | zero => exact hleaf
  | succ n ih =>
    let hl := Nat.lt_of_succ_le hn
    let i : Fin b := ⟨n,hl⟩
    let c (j : Fin k) := RowTrace.state F.system n hl.le (a j) (q.1 j)
    let old (j : Fin k) := F.replayPrivatePrograms store rows number n hl.le (a j)
      (subInitial (view := view) n a initial j) (q.1 j)
    apply step i c q.2 old
    intro j
    exact ih hl.le (a j) (subInitial (view := view) n a initial j) (hleaf j) (q.1 j)

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
