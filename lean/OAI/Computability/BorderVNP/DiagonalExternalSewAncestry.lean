import OAI.Computability.BorderVNP.DiagonalFlatReplay

/-! # Tracing the actual owner of an exterior port through the shortening history

At a parallel node the child number prefixes the saved host. Subdivision
and profile sewing keep each old host at the left summand of the site
type. Storage may then renumber it. These maps identify the host of every
original processor input on the unrenumbered terminal pack as well.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Packing Adaptive CellEntries
open scoped Classical

variable {D : ℕ} {P : Type} {bits : P → ℕ}

/-- The concrete map on original vertices together with the attachment
of every original external port in the retained network. -/
structure Retains (N M : Network D P bits) where
  /-- Address of an original vertex after the layout operation. -/
  site : N.Site ↪ M.Site
  attach : ∀ p, M.attach p = site (N.attach p)

namespace Retains

variable {N M L : Network D P bits}

/-- The original vertex and port addresses. -/
def id (N : Network D P bits) : Retains N N := ⟨.refl _, fun _ => rfl⟩

/-- Compose two stages of the address history. -/
def trans (s : Retains N M) (t : Retains M L) : Retains N L :=
  ⟨s.site.trans t.site,fun p => (t.attach p).trans (congrArg t.site (s.attach p))⟩

/-- The saved live-row layout carries its actual vertex renumbering. -/
def store (s : Storage N M) : Retains N M := ⟨s.site.toEmbedding,s.attach⟩

/-- Initial or inter-epoch geodesic subdivision keeps all old attachments. -/
def subdivide (N : Network D P bits) (routes : N.WireRoutes) : Retains N (N.subdivide routes) :=
  ⟨⟨Sum.inl, Sum.inl_injective⟩,fun _ => rfl⟩

/-- Parallel composition retains each child's address under its own copy number. -/
def parallel {k : ℕ} {N M : Fin k → Network D P bits} (r : ∀ i, Retains (N i) (M i)) :
    Retains (Network.parallel N) (Network.parallel M) :=
  ⟨(Function.Embedding.refl (Fin k)).sigmaMap (fun i => (r i).site),
    fun p => congrArg (Sigma.mk p.1) ((r p.1).attach p.2)⟩

variable {k m d d' : ℕ} [NeZero D] {I B : Type} [Fintype I] [Fintype B] {E : Type*} [Field E]
    (e : PaidIdentity E D m) {child : Fin k → PlacedPack D P bits E I d}

/-- All old external bits attach to the retained vertex in the actual
simultaneous split and profile sewing of the measured step. -/
noncomputable def step (s : PlacedStep m B d' child) (q : s.Index e) :
    Retains (parallelPacks (fun i => (child i).pack)).layout (s.result e q).pack.layout :=
  ⟨⟨Sum.inl,Sum.inl_injective⟩,fun _ => rfl⟩

end Retains

universe u

variable {k m steps : ℕ} [NeZero D] {I E : Type} [Fintype I] [Field E]
    {A : ℕ → Type u} {B : Fin steps → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity E D m}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) E I (depth n)}
    (F : Adaptive.Program (B := B) e view) (save : ProgramStorage F)

/-- Vertex ancestry on the actual stored state at every attained public history. -/
noncomputable def savedAncestry :
    (n : ℕ) → (hn : n ≤ steps) → (a : Leaves k (A 0) n) →
    (q : (F.system.histories n hn a).Index) →
    Retains (parallelLeaves (fun x => (view 0 x).pack) n a).layout (view n (Replay.state F n hn a q)).pack.layout
  | 0, _, _, _ => Retains.id _
  | n+1, hn, a, q => by
    let hj := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let c := fun j : Fin k => Replay.state F n hj.le (a j) (q.1 j)
    exact (Retains.parallel fun j => savedAncestry n hj.le (a j) (q.1 j)).trans
      ((Retains.step e (F.step i c) q.2).trans (Retains.store (save i c q.2)))

/-- The last step is read before its storage renumbering. Earlier steps
follow the attained saved rows. -/
noncomputable def executedAncestry :
    (n : ℕ) → (hn : n ≤ steps) → (a : Leaves k (A 0) n) →
    (q : (F.system.histories n hn a).Index) →
    Retains (parallelLeaves (fun x => (view 0 x).pack) n a).layout
      (F.executed n ((F.system.histories n hn a).term q)).pack.layout
  | 0, _, _, _ => Retains.id _
  | n+1, hn, a, q => by
    let hj := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let c := fun j : Fin k => Replay.state F n hj.le (a j) (q.1 j)
    exact (Retains.parallel fun j => savedAncestry F save n hj.le (a j) (q.1 j)).trans
      (Retains.step e (F.step i c) q.2)

/-- Flattening changes the public names of the ports in both networks;
the retained hosts have the same addresses. -/
def Retains.flat {R : Type*} {n : ℕ} {source target : Pack D (Port k P n) (width bits k n) R}
    (r : Retains source.layout target.layout) :
    Retains (flattenPack n source).layout (flattenPack n target).layout :=
  ⟨r.site,fun z => r.attach ((portEquiv k P n).symm z)⟩

/-- Terminal ancestry in the flat order of the original input array,
on the same physical output used by the geometric estimates. -/
noncomputable def terminalAncestry (a : Fin (k^steps) → A 0) (q : F.Hist a) :
    Retains (flattenPack steps (parallelLeaves (fun x => (view 0 x).pack) steps
      (leavesEquiv k (A 0) steps a))).layout (flattenPack steps (F.terminal a q).pack).layout :=
  (executedAncestry F save steps le_rfl (leavesEquiv k (A 0) steps a) q).flat

section FlatNames

variable {k : ℕ} {X R : Type*} (leaf : X → Pack D P bits R)

/-- The nested disjoint union of the initial sites has the same row-major
leaf numbers as the flat physical array. -/
def originalNames : (n : ℕ) → (flat : Fin (k^n) → X) →
    (parallelLeaves leaf n (leavesEquiv k X n flat)).layout.Site ≃
      (parallelPacks fun i => leaf (flat i)).layout.Site
  | 0, flat => (Equiv.uniqueSigma fun i : Fin 1 => (leaf (flat i)).layout.Site).symm
  | n+1, flat =>
    (Equiv.sigmaCongrRight fun i : Fin k => originalNames n (fun j => flat (copyIndex k n (i,j)))).trans
      (Equiv.sigmaAssocProd.symm.trans (Equiv.sigmaCongrLeft (β := fun i => (leaf (flat i)).layout.Site) (copyIndex k n)))

omit [NeZero D] in
/-- The nested parallel attachment maps to the original host of that flat
leaf, including when many different slots occupy the same vertex. -/
theorem originalNames_attach (n : ℕ) (flat : Fin (k^n) → X) (p : Port k P n) :
    originalNames leaf n flat ((parallelLeaves leaf n (leavesEquiv k X n flat)).layout.attach p) =
      (parallelPacks fun i => leaf (flat i)).layout.attach (portEquiv k P n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨i,p⟩
    let a := fun j => flat (copyIndex k n (i,j))
    exact congrArg (fun z : (j : Fin (k^n)) × (leaf (a j)).layout.Site =>
      (⟨copyIndex k n (i,z.1),z.2⟩ : (parallelPacks fun l => leaf (flat l)).layout.Site))
      (ih a p)

/-- The site map from the original flat input packs to the identically
ordered public ports of the flattened tree. -/
def flatOriginal (n : ℕ) (flat : Fin (k^n) → X) :
    Retains (parallelPacks fun i => leaf (flat i)).layout
      (flattenPack n (parallelLeaves leaf n (leavesEquiv k X n flat))).layout where
  site := (originalNames leaf n flat).symm.toEmbedding
  attach z := by
    let eqv := originalNames leaf n flat
    apply eqv.injective
    change eqv ((parallelLeaves leaf n (leavesEquiv k X n flat)).layout.attach ((portEquiv k P n).symm z)) =
      eqv (eqv.symm ((parallelPacks fun i => leaf (flat i)).layout.attach z))
    rw [eqv.apply_symm_apply]
    exact (originalNames_attach leaf n flat _).trans (congrArg _ ((portEquiv k P n).apply_symm_apply z))

end FlatNames

/-- The final physical site map from the genuinely flat array of original
leaf packs to the measured terminal output of this exact history. -/
noncomputable def terminalHosts (a : Fin (k^steps) → A 0) (q : F.Hist a) :
    Retains (parallelPacks fun i => (view 0 (a i)).pack).layout
      (flattenPack steps (F.terminal a q).pack).layout :=
  (flatOriginal (fun x => (view 0 x).pack) steps a).trans (terminalAncestry F save a q)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
