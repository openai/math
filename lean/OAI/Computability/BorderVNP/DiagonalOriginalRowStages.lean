import OAI.Computability.BorderVNP.DiagonalOriginalRowTree
import OAI.Computability.BorderVNP.DiagonalExternalSewNormalized
import OAI.Computability.BorderVNP.PackedHistoryDenseReady

/-! # Original site numbers in the actual old-row and seed-row rectangles

The stable serializer numbers children in disjoint rectangles, appends the
paid seed template, and retains the same site rows on a dense cable save.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Cover Crossing Shortening Adaptive Packing CellEntries PublicParallel StaticRows
open scoped Classical BorderVNP.Epoch.Cube

variable {D : ℕ} {P : Type} {bits : P → ℕ}

/-- Numeric site rows follow the physical renumbering on save. -/
def carry {N M : Network D P bits} (s : Storage N M) {n : ℕ} (row : N.Site ↪ Fin n) :
    M.Site ↪ Fin n := s.site.symm.toEmbedding.trans row

/-- The saved address of any external port is its actual prior site row. -/
theorem carry_attach {N M : Network D P bits} (s : Storage N M) {n : ℕ} (row : N.Site ↪ Fin n) (p : P) :
    carry s row (M.attach p) = row (N.attach p) := by
  change row (s.site.symm (M.attach p)) = _
  rw [s.attach,s.site.symm_apply_apply]

variable {m k b : ℕ} [NeZero D] {K : Type} [Field K] (e : PaidIdentity K D m)

/-- Public site-row capacities at every inner step of one physical epoch. -/
noncomputable def capacities (k base : ℕ) (seeds : ℕ → ℕ) : ℕ → ℕ
  | 0 => base
  | n+1 => siteCapacity e (k*capacities k base seeds n) (seeds n)

variable {I : Type} [Fintype I] {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (base : ℕ) (seeds : ℕ → ℕ)
    (seed : ∀ i : Fin b, ((I → Deck (depth (i.val+1)+1)) × B i) ↪ Fin (seeds i.val))

/-- Replay the actual ordinary combining step's site directory at every
physical histogram, starting from its true child row embeddings. -/
noncomputable def placed (F : Adaptive.Program (B := B) e view) (save : ProgramStorage F) :
    Step F.system (fun n a => (view n a).pack.layout) (capacities e k base seeds)
      (fun n j => j.val * capacities e k base seeds n) where
  emit n hn c ids q :=
    carry (save ⟨n,hn⟩ c q) (siteRows e (parallelPacks fun j => (view n (c j)).pack)
      (parallelName ids) (seed ⟨n,hn⟩))
  atPort n hn c ids q j p := by
    refine (congrArg Fin.val (carry_attach (save ⟨n,hn⟩ c q) _ (j,p))).trans ?_
    change (ids j ((view n (c j)).pack.layout.attach p)).val + capacities e k base seeds n*j.val =
      j.val*capacities e k base seeds n + (ids j ((view n (c j)).pack.layout.attach p)).val
    ac_rfl

/-- Replay the public stable row operations of a normalized stage, using
the true dense input before appending the fixed seed site rectangle. -/
noncomputable def normalized (F : PackedHistoryCircuit.Normalized.Program (B := B) e view)
    (save : DenseReplay.Saved F) :
    Step F.system (fun n a => (view n a).pack.layout) (capacities e k base seeds)
      (fun n j => j.val * capacities e k base seeds n) where
  emit n hn c ids q :=
    carry (save ⟨n,hn⟩ c q) (siteRows e (F.stage ⟨n,hn⟩ c).input
      (parallelName ids) (seed ⟨n,hn⟩))
  atPort n hn c ids q j p := by
    refine (congrArg Fin.val (carry_attach (save ⟨n,hn⟩ c q) _ (j,p))).trans ?_
    change (ids j ((view n (c j)).pack.layout.attach p)).val + capacities e k base seeds n*j.val =
      j.val*capacities e k base seeds n + (ids j ((view n (c j)).pack.layout.attach p)).val
    ac_rfl

section Directory

open PackedHistoryCircuit.Normalized

variable {d d' s ne : ℕ} {Bin : Type} [Fintype Bin] {child : Fin k → PlacedPack D P bits K (Epoch.Cube D) d}
    (stage : Stage m Bin d' child) (ids : ∀ j, (child j).pack.layout.Site ↪ Fin s)
    (seedID : ((Epoch.Cube D → Deck (d'+1)) × Bin) ↪ Fin ne)
    (dummy : Fin (edgeCapacity e stage.rowCount ne) → SiteShape e stage.input ((Epoch.Cube D → Deck (d'+1)) × Bin))

/-- These are definitionally the site IDs produced by the public sparse
directory and preserved by its next dense save. -/
theorem directory_rows (q : stage.Index e) :
    (stage.directory e (parallelName ids) seedID dummy q).dense.sites =
      siteRows e stage.input (parallelName ids) seedID := rfl

end Directory

end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
