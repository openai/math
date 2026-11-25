import OAI.Computability.BorderVNP.ShortenEnrichedNamedProgram
import OAI.Computability.BorderVNP.DiagonalExternalSewEnriched

/-! # Original site row in a true named combining step

The public sparse row carried by the child is retained with that child's
rectangle offset. Both incoming and outgoing sorts operate on cables. The
saved physical names and the original-port attachment refer to exactly the
same surviving vertex.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing CellEntries
open PackedHistoryCircuit PackedHistoryCircuit.Normalized Shortening.PublicParallel
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

private theorem storedSiteName {D l V E : ℕ} {K P : Type} {bits : P → ℕ}
    (result saved : PlacedPack D P bits K (Cube D) l) (rows : Normalized.Directory result V E)
    (names : Normalized.Directory saved V E) (hs : saved = result.dense rows.cables)
    (hd : HEq names rows.dense) (v : result.pack.layout.Site) :
    let store : Storage result.pack.layout saved.pack.layout := by rw [hs]; exact Storage.dense _ rows.cables
    (names.sites (store.site v)).val = (rows.sites v).val := by
  subst saved
  cases eq_of_heq hd
  rfl

universe u
variable {D m b k : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {source : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ t, source.NamedAt last high V E w P bits k Extra t → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, source.Node last high V E w k i}
variable (r : source.NamedRun last high V E w cap keep hk nodes) (i : Fin b)
    (c : Fin k → NamedState.Admissible (source.NamedGood last high V E w cap keep) i.val)
    (hist : (r.program.stage i c).Index e)

set_option maxHeartbeats 1200000 in
/-- The saved physical row of an arbitrary retained original vertex, including
private boxes with no live attached port. -/
theorem namedSuccessor_site (j : Fin k) (v : (c j).val.placed.pack.layout.Site) :
    let a := r.program.advance i c hist
    let s := (normalizedStage e (r.program.stage i c) hist).trans
      (Retains.store (namesStorage r.program r.saveNames i c hist))
    (a.val.names.sites (s.site ⟨j,v⟩)).val = j.val * V i.val + ((c j).val.names.sites v).val := by
  let step := r.program.stage i c
  let a := r.program.advance i c hist
  calc
    _ = ((r.directory i c hist).sites (.inl ⟨j,v⟩)).val :=
      storedSiteName (step.result e hist) a.val.placed (r.directory i c hist) a.val.names
        (r.stored i c hist) (r.saved_names i c hist) (.inl ⟨j,v⟩)
    _ = _ := (SourcePath.NamedRun.retained_sites source last high V E w cap keep hk r i c hist ⟨j,v⟩).trans (by
      change ((c j).val.names.sites v).val + V i.val*j.val = _
      ac_rfl)

/-- Row-major child offset of the host of each original external port on the
same histogram and the same named state saved by the actual step. -/
theorem namedSuccessor_row (j : Fin k) (p : Port k P i.val) :
    let a := r.program.advance i c hist
    (a.val.names.sites (a.val.placed.pack.layout.attach (j,p))).val =
      j.val * V i.val + ((c j).val.names.sites ((c j).val.placed.pack.layout.attach p)).val := by
  let s := (normalizedStage e (r.program.stage i c) hist).trans (Retains.store (namesStorage r.program r.saveNames i c hist))
  exact (congrArg (fun v => ((r.program.advance i c hist).val.names.sites v).val) (s.attach (j,p))).trans
    (namedSuccessor_site r i c hist j _)

end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
