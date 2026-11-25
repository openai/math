import OAI.Computability.BorderVNP.DiagonalOriginalRowExecution
import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine
import OAI.Computability.BorderVNP.PackedInheritedFlatOrder
import OAI.Computability.BorderVNP.PackedHistoryPrivateSave
import OAI.Computability.BorderVNP.PackedHistorySiteModelRows

/-! # Physical cable and port directories for field models across an epoch

The old input programs pass through the actual initial subdivisions. The
inner row certificate uses these same occupied leaf cables and the returned
outer rectangle uses its terminal cables and flattened free ports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Diagonal.ExternalSew Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P]
    {bits : P → ℕ} {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows)
    {oldCap newCap : ℕ} (oldPort : Port (fan S) P t ↪ Fin oldCap)
    (nextPort : Port (fan S) P (t+1) ↪ Fin newCap)

namespace Epoch

/-- The true occupied rows of an installed input subdivision, transported along
the original pack and realization equalities of this same physical run. -/
noncomputable def installedFieldRows (c : Fin (fan S) → Admissible good t) (i : Fin (fan S)) :
    Rows ((shape t).subdivide ⌈S.budget/S.radius⌉₊) (E.view 0 ((E.run c).flat i)).pack.layout := by
  let run := E.run c
  let a := run.initialSites i
  let orig := RowTrace.sameRows (congrArg Pack.layout (run.originalPack i).symm) (c i).val.rows
  exact RowTrace.sameRows (congrArg (fun p => p.pack.layout) a.realizes.symm) (orig.siteRoutes a.routes S.radius)

/-- Input, inner and return row witnesses for the exact selected outer epoch. -/
structure FieldRows where
  /-- Actual per-stage sparse names in the native normalized program. -/
  layout : E.F.SiteModelRows E.saveNames rows
  /-- The incoming named leaf's cable rectangle has exactly the subdivision capacity. -/
  inputCap : (Fin (fan S) → Admissible good t) → layout.capacity 0 = ((shape t).subdivide ⌈S.budget/S.radius⌉₊).edges
  /-- Its occupied cable rows are the computed subdivision of the actual outer child. -/
  inputRows : ∀ c i z, (layout.edges 0 ((E.run c).flat i) z).val = ((E.installedFieldRows c i).edge z).val
  /-- The returned rectangle has the full terminal cable capacity. -/
  outputCap : (shape (t+1)).edges = layout.capacity S.rounds
  /-- Every true returned cable keeps the row actually stored at the attained terminal state. -/
  outputRows : ∀ c q z, ((E.rows c q).edge z).val = (layout.edges S.rounds ((E.run c).root q) z).val
  /-- The initial input ports are the external ports of the original child. -/
  inputPortCap : rows.nPort 0 = oldCap
  inputPorts : ∀ z, (rows.ports 0 z).val = (oldPort z).val
  /-- The returned port capacity is the terminal port capacity after flattening. -/
  outputPortCap : newCap = rows.nPort S.rounds
  outputPorts : ∀ z, (nextPort z).val = (Flat.portRows S.rounds (rows.ports S.rounds) z).val

end Epoch
end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
