import OAI.Computability.BorderVNP.ShortenEnrichedStages
import OAI.Computability.BorderVNP.ShortenPublicPaddedWords

/-!
# Per-tile record bounds for named dense saves

The installed histogram determines the prior and payload fields of its
successor before any program-wide traversal is chosen. Sorting the result
under the actual destination cable names preserves these fields and their
charges on each tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Epoch Epoch.Round Shortening Packing
open scoped Classical BorderVNP.Epoch.Cube

namespace Stage

variable {D m k d d' V E C : ℕ} [NeZero D] {K : Type*} [Field K]
    {B P : Type} [Fintype B] [Fintype P] {bits : P → ℕ}
    {child : Fin k → PlacedPack D P bits K (Cube D) d} (s : Stage m B d' child)
    (e : PaidIdentity K D m) (hist : s.Index e) (dir : Directory (s.result e hist) V E)

/-- The record fields actually sewn from the children and saved under the
selected destination cable directory. -/
noncomputable def namedSaveFields (data : ∀ i, RecordData (child i).pack.layout) :
    RecordData ((s.result e hist).dense dir.cables).pack.layout where
  prior := s.resultPrior e hist (fun i => (data i).prior)
  payload := s.resultPayload e hist (fun i => (data i).payload)

/-- Both record modes preserve the stage's factor under its named dense save.
The bound holds for the specific sewn fields, including every retained prior
record and private payload charged by the selected histogram. -/
theorem namedSaveFields_within (cert : s.RecordFactor e C) (ex : Bool) (T : ℕ)
    (data : ∀ i, RecordData (child i).pack.layout) (old : ∀ i, RecordsWithin (child i) (data i) ex T) :
    RecordsWithin ((s.result e hist).dense dir.cables) (s.namedSaveFields e hist dir data) ex (C*k*T) := by
  let out := s.result e hist
  let prior := s.resultPrior e hist (fun i => (data i).prior)
  let payload := s.resultPayload e hist (fun i => (data i).payload)
  have bounded := cert hist ex (fun i => (data i).prior) (fun i => (data i).payload) (T-1) (fun i t => by
    have ht := old i t
    change localRecords (child i).pack.layout ex _ _ (fun v => productAddress d ((child i).site v) = t) ≤ T-1
    omega)
  have hc : C*k*(1+(T-1)) = C*k*T := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · have ht := old ⟨0,hk⟩ 1
      have : 1+(T-1) = T := by omega
      rw [this]
  intro t
  let test (v : out.pack.layout.Site) := productAddress d' (out.site v) = t
  have he := Names.localRecords_denseLayout out.pack.layout dir.cables ex prior payload test
  exact (congrArg (1+·) he).le.trans ((bounded t).trans_eq hc)

/-- Existence form of the local record invariant for arbitrary admissible
children and the literal destination directory selected at this histogram. -/
theorem namedSave_records (cert : s.RecordFactor e C) (ex : Bool) (T : ℕ)
    (old : ∀ i, ∃ data, RecordsWithin (child i) data ex T) :
    ∃ data, RecordsWithin ((s.result e hist).dense dir.cables) data ex (C*k*T) := by
  choose data within using old
  exact ⟨_,s.namedSaveFields_within e hist dir cert ex T data within⟩

end Stage

/-- Expanded records over the true product tiles pay for every occupied cable
bit. This bound applies also to uncharged and zero-width cables. -/
theorem widths_of_recordsWithin {D lev cap : ℕ} {P I : Type} [Fintype P] [Fintype I]
    {bits : P → ℕ} {K : Type*} (p : PlacedPack D P bits K I lev) (data : RecordData p.pack.layout)
    (within : RecordsWithin p data true cap) :
    (∑ c, p.pack.layout.width c) ≤ Fintype.card (I → Deck (lev+1))*cap :=
  PublicCapacity.totalWidth_le_records p.pack.layout (fun v => productAddress lev (p.site v))
    data.prior data.payload cap fun t => (Nat.le_add_left _ 1).trans (within t)

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
