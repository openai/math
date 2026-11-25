import OAI.Computability.BorderVNP.PackedHistoryDenseProgram
import OAI.Computability.BorderVNP.ShortenEpochRoundClosure

/-!
# Exact terminal histograms after dense storage

A normalized program returns the publicly stored layout, with the same
external ports and valued tensor as the attained sorted crossing. Its
terminal history directly enumerates these stored networks. When storage
is a dense reindexing, their tracked midpoints remain canonical.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Cover Shortening Packing Adaptive
open scoped Classical

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] {bits : P → ℕ}
variable {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ} {e : PaidIdentity K D m}
variable {view : ∀ j, A j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}

omit [NeZero D] [Field K] in
/-- Saving the output in its sparse public slots preserves the canonical midpoint convention. -/
theorem canonical_dense {d rows : ℕ} (p : PlacedPack D P bits K I d)
    (slot : p.pack.layout.Edge ↪ Fin rows) (hc : p.canonical) : (p.dense slot).canonical := by
  intro e
  obtain ⟨x,rfl⟩ := (Names.denseSlot p.pack.layout slot).surjective e
  rw [(p.dense_marks slot x).2,(p.dense_endpoints slot x).1,(p.dense_endpoints slot x).2]
  exact hc x

namespace Program

variable (F : Program (B := B) e view)

/-- Histograms attained above this actual tuple of publicly ordered leaves. -/
abbrev Hist (flat : Fin (k^b) → A 0) := (F.system.histories b le_rfl (leavesEquiv k (A 0) b flat)).Index

/-- The terminal public state and its site placement, after the actual dense save. -/
noncomputable def terminal (flat : Fin (k^b) → A 0) (i : F.Hist flat) :=
  view b ((F.system.layer b).state ((F.system.histories b le_rfl (leavesEquiv k (A 0) b flat)).term i))

/-- All attained terminal layouts, flattened on the public free labels, preserve the full input tensor. -/
theorem terminal_tensor (flat : Fin (k^b) → A 0) (x : Ports fun z : Fin (k^b) × P => bits z.2) :
    (parallelPacks (fun i => (view 0 (flat i)).pack)).tensor x =
      ∑ i : F.Hist flat, (flattenPack b (F.terminal flat i).pack).tensor x :=
  F.system.tensor_flatHistories _ F.exact b le_rfl flat x

/-- A positive-stage saved state obtained by reindexing the selected sorted output
has the canonical midpoint used in the final rounded-width theorem. -/
theorem saved_canonical
    (slots : ∀ (j : Fin b) (c : Fin k → A j.val) (q : (F.stage j c).Index e),
      Σ r : ℕ, ((F.stage j c).result e q).pack.layout.Edge ↪ Fin r)
    (store : ∀ j c q, view (j.val+1) (F.advance j c q) =
      ((F.stage j c).result e q).dense (slots j c q).2)
    (j : Fin b) (c : Fin k → A j.val) (q : (F.stage j c).Index e) :
    (view (j.val+1) (F.advance j c q)).canonical := by
  exact (congrArg PlacedPack.canonical (store j c q)).mpr (canonical_dense _ _ (fun _ => rfl))

/-- Every attained final history has its canonical geometric midpoint if the last
state was saved by reindexing its true sorted profile. -/
theorem terminal_canonical (hb : 0 < b)
    (store : ∀ (j : Fin b) (c : Fin k → A j.val) (q : (F.stage j c).Index e),
      (view (j.val+1) (F.advance j c q)).canonical)
    (flat : Fin (k^b) → A 0) (i : F.Hist flat) : (F.terminal flat i).canonical := by
  cases b with
  | zero => omega
  | succ j =>
    let z := (F.system.histories (j+1) le_rfl (leavesEquiv k (A 0) (j+1) flat)).term i
    exact store ⟨j,z.2.1.down⟩ (fun a => (F.system.layer j).state (z.1 a)) z.2.2

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
