import OAI.Computability.BorderVNP.PackedHistoryDenseStep
import OAI.Computability.BorderVNP.ShortenMeasuredRound

/-!
# Canonical crossings on the publicly sorted disjoint input

The public allocator sorts the merged input cables by occupied stable rows.
Only the endpoint data and bin tags are transported from the original
cables. The physical placement is rebuilt on the resulting interval
partition, so its hooks refer to precisely the slots selected in that order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch Cover Cover.Frame Framed Adaptive Hecke Packing CombiningStep PackMotions
open BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

namespace CanonicalPlacement

variable {D : ℕ} [NeZero D] {S T P : Type} [Fintype S] [Fintype T]
    {bits : P → ℕ} {K Q : Type*} [PseudoMetricSpace Q] {window : Set (HyperbolicHost (Cube D))}
    {rows : ℕ} (r : S → ℝ) (p : Pack D P bits K) (slot : p.layout.Edge ↪ Fin rows)
    (data : p.layout.Edge → Option (Segment T S window)) (old : p.layout.Site → Q)
    (project : T → HyperbolicHost (Cube D) → Q)

omit [NeZero D] [Fintype S] [Fintype T] in
/-- Relabeling every physical cable transports its two exact endpoint
realizations and true length, before selecting any sorted interval. -/
theorem Realizes.dense (realized : Realizes r p data old project) :
    Realizes r (DirectoryCircuit.densePack p slot) (data ∘ (Names.denseSlot p.layout slot).symm) old project := by
  let ep := Names.denseSlot p.layout slot
  have src (x : p.layout.Edge) : (Names.denseLayout p.layout slot).src (ep x) = p.layout.src x :=
    Names.src_slot p.layout _ _ x
  have dst (x : p.layout.Edge) : (Names.denseLayout p.layout slot).dst (ep x) = p.layout.dst x :=
    Names.dst_slot p.layout _ _ x
  constructor
  · intro c y hc
    obtain ⟨x,rfl⟩ := ep.surjective c
    rw [show (DirectoryCircuit.densePack p slot).layout.src (ep x) = p.layout.src x from src x]
    exact realized.src x y (by change data (ep.symm (ep x)) = some y at hc; rwa [ep.symm_apply_apply] at hc)
  · intro c y hc
    obtain ⟨x,rfl⟩ := ep.surjective c
    rw [show (DirectoryCircuit.densePack p slot).layout.dst (ep x) = p.layout.dst x from dst x]
    exact realized.dst x y (by change data (ep.symm (ep x)) = some y at hc; rwa [ep.symm_apply_apply] at hc)
  · intro c y hc
    obtain ⟨x,rfl⟩ := ep.surjective c
    rw [show (DirectoryCircuit.densePack p slot).layout.src (ep x) = p.layout.src x from src x,
      show (DirectoryCircuit.densePack p slot).layout.dst (ep x) = p.layout.dst x from dst x]
    exact realized.length x y (by change data (ep.symm (ep x)) = some y at hc; rwa [ep.symm_apply_apply] at hc)

end CanonicalPlacement

namespace PreparedBins

variable {D m d n k rows : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
    (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
    (slot : (raw child).layout.Edge ↪ Fin rows)

/-- Carried tags from the actual sampled children, before stable row sorting. -/
noncomputable abbrev publicBin :=
  jointBin (fun i => (child i).pack)
    (B.tag (d := d+1) (n := n) (fun i => (child i).pack) (fun i => (child i).active) L.kind L.lift) ω

/-- Exact type of the installation on the publicly reordered merged pack. -/
abbrev DensePlacement (m : ℕ) := Placement (m := m) (DirectoryCircuit.densePack (raw child) slot)
  (CutCircuit.denseBin (raw child).layout slot (B.publicBin child L ω))
  (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart) (Cube D) (SurfaceHost (Cube D) (d+1))

/-- The physical stage selected by the public motion and the actual stable
input row injection. The permutation ranks the entire merged pack. -/
noncomputable def densePlacedStep (g : B.DensePlacement child L ω slot m) :
    Stage m B.Bin d child where
  rowCount := rows
  slot := slot
  bin := B.publicBin child L ω
  perm := CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart
  positive := fun _ => true
  placed := g

omit [Field K] in
set_option maxHeartbeats 1000000 in
/-- At every sufficiently deep quotient and every sampled motion, the
actually sorted interval allocator has a fitted physical placement. Its
endpoint lifts are constructed from its own selected edges. -/
theorem dense_fitted {θ : ℝ} (hh : 0 ≤ h) (hη : η ≤ θ/4) :
    ∃ floor : ℕ, ∀ d ≥ floor, ∀ {n m k rows : ℕ} {P : Type} {bits : P → ℕ}
    (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
    (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
    (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
    (slot : (raw child).layout.Edge ↪ Fin rows), ∃ g : B.DensePlacement child L ω slot m,
      g.old = movedOld (fun i => (child i).pack) ω (childSites child) ∧
      g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart ∧
      g.project = (fun a => tileProject a.1) ∧
      let s := B.densePlacedStep child L ω slot g
      g.fits s.input s.label s.perm s.orient h θ := by
  obtain ⟨floor,realizes⟩ := parallel_realizes (D := D) (K := K) (S := B.types) (2*h) (by linarith)
  refine ⟨floor,?_⟩
  intro d hd n m k rows P bits child L ω slot
  let input := fun i => (child i).pack
  let active := fun i => (child i).active
  let shape := fun w : Active input active => (L.kind w).val
  let r := fun t : B.types => t.val.radius
  let old := movedOld input ω (childSites child)
  let data := parallelData input active L.kind shape L.lift ω
  let p := raw child
  let ep := Names.denseSlot p.layout slot
  have re := realizes (d+1) (by omega) n k input active L.kind shape L.lift ω r (childSites child)
    (fun _ => rfl) (fun w => mul_le_mul_of_nonneg_left (B.short _ (L.kind w).property) (by norm_num))
    L.src L.dst
  have rd := re.dense r p slot data old tileProject
  have hbin : CanonicalPlacement.bin r B.chart (DirectoryCircuit.densePack p slot) (data ∘ ep.symm) =
      CutCircuit.denseBin p.layout slot (B.publicBin child L ω) :=
    congrArg (fun tag => tag ∘ ep.symm) (parallel_bin input active L.kind shape L.lift ω r B.chart)
  have fitted := CanonicalPlacement.exists_placement (m := m) r B.chart (DirectoryCircuit.densePack p slot)
    (data ∘ ep.symm) old tileProject tileProject_nonexpanding rd
    (fun t => ⟨t.val.positive.le,B.short _ t.property⟩) hη
  rw [hbin] at fitted
  obtain ⟨g,hg,hc,hp,hfit⟩ := fitted
  exact ⟨g,hg,hc,hp,hfit⟩

end PreparedBins
end Shortening

end BorderVNP
end Computability
end OAI
