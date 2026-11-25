import OAI.Computability.BorderVNP.PackedHistoryPrivateSave
import OAI.Computability.BorderVNP.PackedHistorySiteModelRows
import OAI.Computability.BorderVNP.PackedHistoryLeafPrograms
import OAI.Computability.BorderVNP.PackedInheritedFlatValue

/-! # Local field models of the original adaptive private histories

At each selected ordinal the complete private tapes are read in the physical
cable and port order certified by the saved public state. A leafwise field
model therefore persists through every actual program update, stable sort,
and the final flattening of the exterior ports.
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
  (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows)
  (layout : F.SiteModelRows store rows) (number : e.Entry → ℕ) (values : ℕ → K)

/-- The physical factor models at a named state, including each program's locality. -/
def SiteModelRows.models (n : ℕ) (x : A n) (programs : Site.Programs (view n x).pack.layout) : Prop :=
  Site.Programs.FieldModels (view n x).pack (layout.edges n x) (rows.ports n) programs values

/-- Original normalized replay at any attained histogram, assuming only genuine
field identities at its leaves, the actual paid constants, and the public row receipt. -/
theorem replayPrivatePrograms_models (paid : ∀ i, values (number i) = e.entry i)
    (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout)
    (start : LeavesWithin (view := view) (layout.models F store rows values) n a initial)
    (q : (F.system.histories n hn a).Index) :
    layout.models F store rows values n (RowTrace.state F.system n hn a q)
      (F.replayPrivatePrograms store rows number n hn a initial q) := by
  apply F.replayPrivatePrograms_invariant store rows number _ _ n hn a initial start q
  intro i c hist old h
  exact F.savePrivatePrograms_models store rows number i c hist old
    (fun j => layout.edges i.val (c j)) (layout.inputCap i c) (layout.inputRows i c)
    (layout.edges _ (F.advance i c hist)) (layout.savedCap i c hist) (layout.savedRows i c hist)
    (layout.portCap i) (layout.portRows i) values paid h

/-- The saved programs realize every local field factor on the selected original
histogram, from the physical models of its independently supplied flat leaf tapes. -/
theorem joined_replay_models (paid : ∀ i, values (number i) = e.entry i)
    (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (initial : ∀ z, Site.Programs (view 0 (flat z)).pack.layout)
    (leaf : ∀ z, layout.models F store rows values 0 (flat z) (initial z))
    (q : (F.system.histories n hn (leavesEquiv k _ n flat)).Index) :
    layout.models F store rows values n (RowTrace.state F.system n hn (leavesEquiv k _ n flat) q)
      (F.replayPrivatePrograms store rows number n hn (leavesEquiv k _ n flat)
        (nestedPrivatePrograms (fun x => (view 0 x).pack) n flat initial) q) :=
  F.replayPrivatePrograms_models store rows layout number values paid n hn _ _
    (nestedLeaves_within view _ n flat initial leaf) q

/-- At the terminal of the actual inner execution, every private site
realizes its physical table on the true flattened copy ports. -/
theorem flatPrivatePrograms_models (paid : ∀ i, values (number i) = e.entry i)
    (flat : Fin (k^b) → A 0) (initial : ∀ z, Site.Programs (view 0 (flat z)).pack.layout)
    (leaf : ∀ z, layout.models F store rows values 0 (flat z) (initial z)) (q : F.Hist flat) :
    let x := RowTrace.state F.system b le_rfl (leavesEquiv k _ b flat) q
    let p := (F.terminal flat q).pack
    Site.Programs.FieldModels (flattenPack b p) (layout.edges b x) (Flat.portRows b (rows.ports b))
      (F.flatPrivatePrograms store rows number flat initial q) values := by
  intro x p
  let src := nestedPrivatePrograms (fun z => (view 0 z).pack) b flat initial
  let prog := F.replayPrivatePrograms store rows number b le_rfl (leavesEquiv k _ b flat) src q
  have hm : Site.Programs.FieldModels p (layout.edges b x) (rows.ports b) prog values :=
    F.joined_replay_models store rows layout number values paid b le_rfl flat initial leaf q
  intro v
  refine ⟨(hm v).1,?_⟩
  exact Site.Models.flattenPack b p (layout.edges b x) (rows.ports b) v (prog v).program
    (prog v).size (fieldWeight values) (hm v).2

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
