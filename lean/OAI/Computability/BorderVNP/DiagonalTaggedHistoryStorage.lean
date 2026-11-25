import OAI.Computability.BorderVNP.DiagonalTaggedStep
import OAI.Computability.BorderVNP.ShortenPhysicalClosed

/-! # Saving tagged tables at adaptive shortening nodes

The public placement can renumber the occupied cable rows before the next
round reads them. The map on assignments records the actual bits at those
rows. It therefore transports arbitrary local tables, including both the
gadget counters and the selected unary power bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Packing
open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ}

/-- An actual renumbering of a layout. Vacant slots may be present in the
saved array, provided a word assignment on the saved rows is uniquely
determined by its bits on the occupied rows. -/
structure Storage (N M : Network D P bits) where
  /-- The physical host address of every original site. -/
  site : N.Site ≃ M.Site
  /-- The occupied saved row for every original cable. -/
  edge : N.Edge ↪ M.Edge
  src : ∀ e, M.src (edge e) = site (N.src e)
  dst : ∀ e, M.dst (edge e) = site (N.dst e)
  width : ∀ e, M.width (edge e) = N.width e
  attach : ∀ p, M.attach p = site (N.attach p)
  position : ∀ v, M.position (site v) = N.position v
  /-- The complete original cable words determined by the saved rows. -/
  assignment : M.Assignment ≃ N.Assignment
  bit : ∀ (a : M.Assignment) e j, assignment a e j = a (edge e) (Fin.cast (width e).symm j)

namespace Storage

variable {N M L : Network D P bits}

/-- A node that retains the just-computed pack at its original addresses. -/
def id (N : Network D P bits) : Storage N N where
  site := Equiv.refl _
  edge := Function.Embedding.refl _
  src _ := rfl
  dst _ := rfl
  width _ := rfl
  attach _ := rfl
  position _ := rfl
  assignment := Equiv.refl _
  bit _ _ _ := rfl

/-- A bijective renumbering of the physical vertices and edges. The
assignment equivalence is derived from the cable permutation and widths. -/
def renumber (vertices : N.Site ≃ M.Site) (cables : N.Edge ≃ M.Edge)
    (source : ∀ e, M.src (cables e) = vertices (N.src e))
    (target : ∀ e, M.dst (cables e) = vertices (N.dst e))
    (width : ∀ e, M.width (cables e) = N.width e)
    (ports : ∀ p, M.attach p = vertices (N.attach p))
    (placed : ∀ v, M.position (vertices v) = N.position v) : Storage N M where
  site := vertices
  edge := cables.toEmbedding
  src := source
  dst := target
  width := width
  attach := ports
  position := placed
  assignment := (Equiv.piCongrLeft (fun e => Fin (M.width e) → Bool) cables).symm.trans
    (Equiv.piCongrRight fun e => (finCongr (width e)).arrowCongr (Equiv.refl Bool))
  bit _ _ _ := rfl

/-- Two successive renumberings compose on sites, physical cable addresses,
and the binary words read there. -/
def trans (s : Storage N M) (t : Storage M L) : Storage N L where
  site := s.site.trans t.site
  edge := s.edge.trans t.edge
  src e := (t.src _).trans (congrArg t.site (s.src e))
  dst e := (t.dst _).trans (congrArg t.site (s.dst e))
  width e := (t.width _).trans (s.width e)
  attach p := (t.attach p).trans (congrArg t.site (s.attach p))
  position v := (t.position _).trans (s.position v)
  assignment := t.assignment.trans s.assignment
  bit a e j := (s.bit _ e j).trans (t.bit a _ _)

/-- Save real cables in designated public rows, with zero-width dummy loops
in any remaining slots. -/
noncomputable def rows (N : Network D P bits) {r : ℕ}
    (number : N.Edge ↪ Fin r) (dummy : Fin r → N.Site) :
    Storage N (Names.layout N number dummy) where
  site := Equiv.refl _
  edge := ⟨Names.slot N number, fun {e f} h => number.injective (Fin.ext <|
    (Names.cableName_slot N number dummy e).symm.trans <|
      (congrArg (SeedIntervals.cableName (Names.layout N number dummy)) h).trans
        (Names.cableName_slot N number dummy f))⟩
  src := Names.src_slot N number dummy
  dst := Names.dst_slot N number dummy
  width := Names.width_slot N number dummy
  attach _ := rfl
  position _ := rfl
  assignment := Names.assignmentEquiv N number dummy
  bit _ _ _ := rfl

/-- The actual dense presentation ordered by its stable public row numbers. -/
noncomputable def dense (N : Network D P bits) {r : ℕ} (number : N.Edge ↪ Fin r) :
    Storage N (Names.denseLayout N number) :=
  rows N (Names.denseRank N number).toEmbedding (fun i => N.src ((Names.denseRank N number).symm i))

/-- A dense save uses exactly the allocator's occupied edge address. -/
theorem dense_edge (N : Network D P bits) {r : ℕ} (number : N.Edge ↪ Fin r) (e : N.Edge) :
    (dense N number).edge e = Names.denseSlot N number e := rfl

variable (s : Storage N M)

/-- Relabel each local incidence by the actual stored edge. Both endpoints
continue to read the same bit position. -/
def tables {R : Type*} (T : N.Tables R) : M.Tables R := fun v z x =>
  T (s.site.symm v)
    (fun e j => z ⟨s.edge e.val, e.property.imp
      (fun h => (s.src e.val).trans ((congrArg s.site h).trans (s.site.apply_symm_apply v)))
      (fun h => (s.dst e.val).trans ((congrArg s.site h).trans (s.site.apply_symm_apply v)))⟩
      (Fin.cast (s.width e.val).symm j))
    (fun p => x ⟨p.val, (s.attach p.val).trans
      ((congrArg s.site p.property).trans (s.site.apply_symm_apply v))⟩)

/-- The generic local transport is the packed row reader used by the
physical layout. -/
theorem tables_rows {R : Type*} (N : Network D P bits) {r : ℕ}
    (number : N.Edge ↪ Fin r) (dummy : Fin r → N.Site) (T : N.Tables R) :
    (rows N number dummy).tables T = Names.tables N number dummy T := rfl

/-- Pointwise interpretation commutes with renumbering, for arbitrary local
entries and any interpretation function. -/
theorem tables_map {R S : Type*} (f : R → S) (T : N.Tables R) :
    s.tables (fun v z x => f (T v z x)) = fun v z x => f (s.tables T v z x) := rfl

/-- Restricting a complete stored assignment reads the original site on
the corresponding old assignment. -/
theorem read {R : Type*} (T : N.Tables R) (a : M.Assignment) (x : Ports bits) (v : M.Site) :
    M.read (s.tables T) a x v = N.read T (s.assignment a) x (s.site.symm v) := by
  unfold Network.read tables
  congr 1
  funext e j
  exact (s.bit a e.val j).symm

/-- Tensor preservation for *every* family of local tables, with the same
external ports and the exact finite sum over cable words. -/
theorem value {R : Type*} [CommSemiring R] (T : N.Tables R) (x : Ports bits) :
    M.value (s.tables T) x = N.value T x := by
  unfold Network.value
  refine Fintype.sum_equiv s.assignment _ _ fun a => ?_
  exact Fintype.prod_equiv s.site.symm _ _ fun v => s.read T a x v

/-- Reading a stored power bit uses the renumbered host of that same
original unary factor. -/
def words {Team Param Gadget : Type*} [Fintype Team] [Fintype Param] {b : ℕ}
    {tags : N.Tables (Entry Param Gadget)} (w : PowerWords Team Param Gadget b N tags) :
    PowerWords Team Param Gadget b M (s.tables tags) where
  site i := s.site (w.site i)
  selected := s.tables w.selected
  located v _ _ i h := (congrArg s.site (w.located (s.site.symm v) _ _ i h)).trans
    (s.site.apply_symm_apply v)
  exact v _ _ := w.exact (s.site.symm v) _ _

/-- Renumbering the stored integer tags commutes with polynomial contraction
for all gadget values, including vanishing values. -/
theorem interpret_tensor {Param Gadget E : Type*} [Field E]
    (values : Gadget → E) (tags : N.Tables (Entry Param Gadget)) (x : Ports bits) :
    (interpretPack values ⟨M,s.tables tags⟩).tensor x = (interpretPack values ⟨N,tags⟩).tensor x :=
  s.value (fun v z p => interpret values (tags v z p)) x

section TrackedStorage

variable {P : Type} {bits : P → ℕ} {N M : Network D P bits} (s : Storage N M)
    {Team Param Gadget : Type*} [Fintype Team] [Fintype Param] {b : ℕ}

/-- Store the conditioned factors and the original unary positions together
on precisely the same saved layout. -/
def tracked (t : Tracked Team Param Gadget b N) : Tracked Team Param Gadget b M :=
  ⟨s.tables t.tags, s.words t.words⟩

/-- Every interpretation of a stored conditioned pack gives the original
contraction for each exterior bit assignment. -/
theorem tracked_tensor {E : Type*} [CommSemiring E] (t : Tracked Team Param Gadget b N)
    (values : Gadget → E) (x : Ports bits) :
    ((s.tracked t).valued values).tensor x = (t.valued values).tensor x :=
  s.value (fun v z p => interpret values (t.tags v z p)) x

end TrackedStorage
end Storage

universe u

open Shortening.Adaptive

variable {m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {A : ℕ → Type u} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}

/-- The explicit saved layout at every attained step of this adaptive program. -/
abbrev ProgramStorage (F : Adaptive.Program (B := B) e view) :=
  ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.step i c).Index e),
    Storage ((F.step i c).result e q).pack.layout (view (i.val+1) (F.advance i c q)).pack.layout

/-- Storing the direct result of every step needs only equality of the
physical layouts. All table and word preservation then follows from the
identity address map. -/
noncomputable def ProgramStorage.ofLayoutEq (F : Adaptive.Program (B := B) e view)
    (direct : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.step i c).Index e),
      ((F.step i c).result e q).pack.layout = (view (i.val+1) (F.advance i c q)).pack.layout) :
    ProgramStorage F :=
  fun i c q => (direct i c q) ▸ Storage.id _

/-- The concrete closed geometric recursion stores each newly sewn pack
itself, hence transports every tag and every power bit by the identity. -/
noncomputable def ProgramStorage.ofClosed (e : PaidIdentity K D m)
    (good : ∀ n, PlacedPack D (Port k P n) (width bits k n) K I (depth n) → Prop)
    (step : ∀ (i : Fin b) (c : Fin k → Adaptive.Program.Prepared good i.val),
      PlacedStep m (B i) (depth (i.val+1)) (fun j => (c j).val))
    (closed : ∀ (i : Fin b) (c : Fin k → Adaptive.Program.Prepared good i.val)
      (q : (step i c).Index e), good (i.val+1) ((step i c).result e q)) :
    ProgramStorage (Adaptive.Program.ofClosed e good step closed) :=
  fun _ _ _ => Storage.id _

/-- Store a node by its dense live row order. The witness uses the actual
sparse cable numbers chosen at that node and only requires identifying the
resulting layout with the successor's physical layout. -/
noncomputable def ProgramStorage.ofDense (F : Adaptive.Program (B := B) e view)
    (size : ∀ (i : Fin b) (c : Fin k → A i.val), (F.step i c).Index e → ℕ)
    (number : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.step i c).Index e),
      ((F.step i c).result e q).pack.layout.Edge ↪ Fin (size i c q))
    (saved : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.step i c).Index e),
      Names.denseLayout ((F.step i c).result e q).pack.layout (number i c q) =
        (view (i.val+1) (F.advance i c q)).pack.layout) : ProgramStorage F :=
  fun i c q => (saved i c q) ▸ Storage.dense _ (number i c q)

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
