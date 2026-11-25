import OAI.Computability.BorderVNP.PackedOuterCompilerRows
import OAI.Computability.BorderVNP.PackedHistorySignFree

/-! # Positive weights of private assignments in the attained terminal cells

All actual original, subdivision, crossing and paid private factors have
positive observation signs. The source coefficients travel as reported
field entries. The terminal private assignment therefore contributes one
exactly when the box observations, wiring records and count words agree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxRecDepth 2500
set_option maxHeartbeats 1600000

universe u

variable {D m start T : ℕ} [NeZero D] {P K : Type} [Fintype P] [Field K] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start}

namespace Epoch

variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows)
    (c : Fin (fan S) → Admissible good t) (old : ∀ i, Site.Programs (c i).val.pack.layout)

set_option maxHeartbeats 1200000 in
/-- The actual physical subdivision and dense stored child layouts retain
positive observations at the start of each selected epoch. -/
theorem installedPrivatePrograms_signFree (h : ∀ j v, (old j v).program.SignFree) (i : Fin (fan S)) :
    ∀ v, (E.installedPrivatePrograms rows c old i v).program.SignFree := by
  let run := E.run c
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) a.realizes.symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let prior := samePrivatePrograms orig (old i)
  have hp := samePrivatePrograms_forall Site.SignFree orig (old i) (h i)
  let src : Site.Programs (P := Port S.fanIn (Port (fan S) P t) 0) a.pack.layout :=
    changePrivateInstance a.pack.layout prior
  let sub := Subdivision.subdividePrivatePrograms (P := Port S.fanIn (Port (fan S) P t) 0)
    a.pack.layout (a.routes.routes S.radius) raw.edge new.edge (rows.ports 0) src
  have hs (v) : (src v).program.SignFree := hp v
  have hz := Subdivision.subdividePrivatePrograms_signFree (P := Port S.fanIn (Port (fan S) P t) 0)
    a.pack.layout (a.routes.routes S.radius) raw.edge new.edge (rows.ports 0) src hs
  exact samePrivatePrograms_forall (P := Port S.fanIn (Port (fan S) P t) 0) Site.SignFree saved sub hz

/-- Each genuine returned histogram carries positive private observation
signs, independently of the numerical values of the paid entries. -/
theorem privatePrograms_signFree (number : e.Entry → ℕ) (h : ∀ j v, (old j v).program.SignFree)
    (q : E.F.Hist (E.run c).flat) : ∀ v, (E.privatePrograms rows c old number q v).program.SignFree :=
  E.F.flatPrivatePrograms_signFree E.saveNames rows number (E.run c).flat (E.installedPrivatePrograms rows c old) q
    (E.installedPrivatePrograms_signFree rows c old h)

end Epoch

namespace Machine

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)
    (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

/-- Every site on every selected outer history has positive private
observation signs. -/
theorem historyPrivatePrograms_signFree (h : ∀ v, (base v).program.SignFree)
    (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index) :
    ∀ v, (M.historyPrivatePrograms rows number bottom base n hn q v).program.SignFree :=
  M.historyPrivatePrograms_forall rows number bottom base (fun _ => Site.SignFree)
    (fun n hn c old prior => (M n hn).privatePrograms_signFree (rows n hn) c old number prior) h n hn q

variable (q : (packHistory bottom M.epoch T).Index)
/-- The physically flattened terminal host retains the positive signs of its
current program on the selected outer history. -/
theorem terminalPrivatePrograms_signFree (h : ∀ v, (base v).program.SignFree) :
    ∀ v, (M.terminalPrivatePrograms rows number bottom base q v).program.SignFree :=
  M.historyPrivatePrograms_signFree rows number bottom base h T le_rfl q

/-- The actual final owner-sorted cell directory has no private sign toggle,
including all original site tables and all selected paid tables. -/
theorem terminalDirectory_signFree (h : ∀ v, (base v).program.SignFree) :
    let N := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
    let state := fun v => (M.terminalPrivatePrograms rows number bottom base q v).program
    ∀ {ns ne np : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
      (portID : Fin ((fan S)^T) × P ↪ Fin np) (owner : Fin ns → ℕ) (cell : N.Site → ℕ)
      (c : ℕ) (reports : List (List ℕ)),
      (FinalCell.directory owner N cell siteID edgeID portID state c reports).SignFree := by
  intro N state ns ne np siteID edgeID portID owner cell c reports
  exact sortedDirectory_signFree N cell siteID edgeID portID owner state c reports
    (M.terminalPrivatePrograms_signFree rows number bottom base q h)

/-- For the actual complete bit assignment, the local signed contribution
is exactly the indicator of the passing observations, wiring and counts. -/
theorem terminalDirectory_weight_eq (h : ∀ v, (base v).program.SignFree) :
    let N := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
    let state := fun v => (M.terminalPrivatePrograms rows number bottom base q v).program
    ∀ {ns ne np : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
      (portID : Fin ((fan S)^T) × P ↪ Fin np) (owner : Fin ns → ℕ) (cell : N.Site → ℕ)
      (c : ℕ) (reports : List (List ℕ)) (bank : ℕ → Bool),
      let dir := FinalCell.directory owner N cell siteID edgeID portID state c reports
      dir.weight bank = if ∃ os, dir.observations bank = some os ∧
        (∀ r ∈ dir.records, r.Valid dir.boxes bank) ∧ CellSparse.countsValid bank reports os then 1 else 0 := by
  intro N state ns ne np siteID edgeID portID owner cell c reports bank dir
  exact (M.terminalDirectory_signFree rows number bottom base q h siteID edgeID portID owner cell c reports).weight_eq bank

end Machine

end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
