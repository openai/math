import OAI.Computability.BorderVNP.PackedInheritedWorkStep
import OAI.Computability.BorderVNP.PackedInheritedFlatOrder
import OAI.Computability.BorderVNP.PackedInheritedParallelOrder
import OAI.Computability.BorderVNP.ShortenPublicSubdivisionRows

/-! # Static port columns throughout the work-width replay

An argument keeps its host row through a subdivision and dense save. When
child rectangles are concatenated its new public host row acquires only
the child's rectangle offset. Thus the incidence scan can use constant
argument pointer/width columns fixed before any histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.StaticRows Shortening.PublicParallel Shortening.PublicCapacity
open Shortening.Adaptive Cover Epoch Epoch.Round PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

/-- Public exterior pointer and width columns, independent of the selected histogram. -/
structure Ports (n : ℕ) where
  /-- Site row stored as the attachment pointer for each port slot. -/
  host : Fin n → ℕ
  /-- Width in bits of the port at each slot, including zero-width vacant slots. -/
  width : Fin n → ℕ

/-- Physical correctness of the static port columns, including unoccupied
slots. The host field of an empty port is irrelevant to the virtual scan. -/
structure Ports.Reads {n V D : ℕ} (p : Ports n) {P : Type} {bits : P → ℕ}
    (N : Network D P bits) (sites : N.Site ↪ Fin V) (id : P ↪ Fin n) : Prop where
  attach : ∀ a, p.host (id a) = (sites (N.attach a)).val
  size : ∀ a, p.width (id a) = bits a
  hole : ∀ i, i ∉ Set.range id → p.width i = 0

/-- The fixed port header of a parallel/sewn stage. The child pointer
offsets use the entire public site rectangle, including holes. -/
def Ports.parallel {n : ℕ} (p : Ports n) (k V : ℕ) : Ports (k*n) where
  host i := let z := finProdFinEquiv.symm i; z.1.val*V+p.host z.2
  width i := p.width (finProdFinEquiv.symm i).2

variable {D m k V E n np d lev : ℕ} [NeZero D] {K Bin P : Type} [Field K] [Fintype Bin] {bits : P → ℕ}
variable {child : Fin k → PlacedPack D P bits K (Cube D) d}
variable (e : PaidIdentity K D m) (s : Stage m Bin lev child) (q : s.Index e)
variable (names : ∀ i, (child i).pack.layout.Site ↪ Fin V)
variable (seed : ((Cube D → Deck (lev+1)) × Bin) ↪ Fin n)
variable (pdir : Directory (s.result e q) (siteCapacity e (k*V) n) E)
variable (p : Ports np) (id : P ↪ Fin np)

/-- Static exterior words of the selected dense output, obtained entirely
from the input columns and the fixed row-major placement. -/
theorem Ports.sewn (hs : pdir.sites = siteRows e s.input (parallelName names) seed)
    (old : ∀ i, p.Reads (child i).pack.layout (names i) id)
    (holes : ∀ i, i ∉ Set.range id → p.width i = 0) :
    (p.parallel k V).Reads ((s.result e q).dense pdir.cables).pack.layout pdir.dense.sites (Parallel.portRows k id) := by
  have pair (i : Fin k) (a : P) : finProdFinEquiv.symm (Parallel.portRows k id (i,a)) = (i,id a) :=
    finProdFinEquiv.symm_apply_apply _
  constructor
  · rintro ⟨i,a⟩
    simp only [Ports.parallel,pair,(old i).attach,Directory.dense_sites,hs]
    change i.val*V+(names i ((child i).pack.layout.attach a)).val = (names i ((child i).pack.layout.attach a)).val+V*i.val
    ac_rfl
  · rintro ⟨i,a⟩
    simpa only [Ports.parallel,pair] using (old i).size a
  · intro z hz
    obtain ⟨⟨i,r⟩,rfl⟩ := finProdFinEquiv.surjective z
    have hr : r ∉ Set.range id := by rintro ⟨a,rfl⟩; exact hz ⟨(i,a),rfl⟩
    simpa only [Ports.parallel,Equiv.symm_apply_apply] using holes r hr

variable {s₀ : Shape} (N : Network D P bits) (rows : Rows s₀ N) (route : N.WireRoutes)
    (extra : ℕ) (fits : ∀ e, route.interior e ≤ extra)

omit [NeZero D] in
/-- Subdivision leaves the argument pointers at the original retained sites. -/
theorem Ports.subdivide (old : p.Reads N rows.site id) :
    p.Reads (N.subdivide route) (rows.subdivide route extra fits).site id := by
  exact ⟨old.attach,old.size,old.hole⟩

omit [NeZero D] [Field K] in
/-- Flattening an inner epoch only changes the exterior argument type. Its
source header and all its numerical row values are reused. -/
theorem Ports.flatten {b : ℕ} (pack : Pack D (Port k P b) (Adaptive.width bits k b) K)
    (sites : pack.layout.Site ↪ Fin V) (port : Port k P b ↪ Fin np) (old : p.Reads pack.layout sites port) :
    p.Reads (flattenPack b pack).layout sites (Flat.portRows b port) := by
  constructor
  · intro a; exact old.attach ((portEquiv k P b).symm a)
  · intro a
    change p.width (port ((portEquiv k P b).symm a)) = bits a.2
    simpa only [Equiv.apply_symm_apply] using (old.size ((portEquiv k P b).symm a)).trans (width_portEquiv bits k b _)
  · intro i hi
    apply old.hole i
    rintro ⟨u,rfl⟩
    apply hi
    exact ⟨portEquiv k P b u,congrArg port ((portEquiv k P b).symm_apply_apply u)⟩

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
