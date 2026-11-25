import OAI.Computability.BorderVNP.PackedOuterBirthCases
import OAI.Computability.BorderVNP.PackedProgramBoxRoster

/-! # A fixed public box directory throughout the enriched outer history

The whole epoch's physical serializer realizes the same reserved body list at
each attained profile, including unoccupied row numbers. Recursing over the
actual histogram tuple then realizes the same list on each complete history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1400000
universe u

variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)
    (known : ∀ n, Fin (shape n).sites → List (List CellSparse.Factor))

/-- Carry the branch-independent physical site roster through the true outer profile
index and its returned directory, preserving both occupied rows and holes. -/
theorem stepPrivatePrograms_roster {n : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (old : ∀ j, Site.Programs (c j).val.pack.layout)
    (step : ∀ q, BoxRoster.Realizes (((M n hn).term c q).val.rows.site)
      (fun v => ((M n hn).privatePrograms (rows n hn) c old number q v).program.boxes) (known (n+1)))
    (q : (M.epoch n c).Index) :
    BoxRoster.Realizes ((M.epoch n c).term q).val.rows.site
      (fun v => (M.stepPrivatePrograms rows number hn c old q v).program.boxes) (known (n+1)) := by
  let family (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) → Site.Programs (z.term j).val.pack.layout
  have carry {z y : ProfileSum (Admissible good (n+1))} (he : z=y) (f : family y)
      (h : ∀ j : y.Index, BoxRoster.Realizes (y.term j).val.rows.site (fun v => (f j v).program.boxes) (known (n+1))) :
      ∀ j : z.Index, BoxRoster.Realizes (z.term j).val.rows.site
        (fun v => ((Eq.mpr (congrArg family he) f) j v).program.boxes) (known (n+1)) := by
    subst y
    exact h
  have he : M.epoch n c = (M n hn).choice c := dite_eq_left hn
  exact carry he ((M n hn).privatePrograms (rows n hn) c old number) step q

variable (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

/-- A roster chosen independently of the outer histogram is realized at every actual
stored row, following the incoming child tuple of that very profile. -/
theorem historyPrivatePrograms_roster
    (initial : BoxRoster.Realizes bottom.val.rows.site (fun v => (base v).program.boxes) (known 0))
    (step : ∀ (n : ℕ) (hn : n<T) (c : Fin (fan S) → Admissible good n)
      (old : ∀ j, Site.Programs (c j).val.pack.layout),
      (∀ j, BoxRoster.Realizes (c j).val.rows.site (fun v => (old j v).program.boxes) (known n)) →
      ∀ q, BoxRoster.Realizes (((M n hn).term c q).val.rows.site)
        (fun v => ((M n hn).privatePrograms (rows n hn) c old number q v).program.boxes) (known (n+1)))
    (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index) :
    BoxRoster.Realizes ((packHistory bottom M.epoch n).term q).val.rows.site
      (fun v => (M.historyPrivatePrograms rows number bottom base n hn q v).program.boxes) (known n) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    let hl := Nat.lt_of_succ_le hn
    let c := fun j : Fin (fan S) => (packHistory bottom M.epoch n).term (q.1 j)
    let old := fun j : Fin (fan S) => M.historyPrivatePrograms rows number bottom base n hl.le (q.1 j)
    exact M.stepPrivatePrograms_roster rows number known hl c old (step n hl c old (fun j => ih hl.le (q.1 j))) q.2

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
