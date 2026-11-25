import OAI.Computability.BorderVNP.ShortenPublicParallelNames
import OAI.Computability.BorderVNP.ShortenPublicSegmentStage
import OAI.Computability.BorderVNP.ShortenPublicEndpointDense

/-!
# Feeding independently compiled successor packs into the next stage

All child outputs are constructed once on the shared input. The merge adds
the rectangle offsets to their endpoint words. Its joined table supplies the
actual fields required by the next round's catalog reader. The stable names
also remain valid for the densely ranked layout used by the interval allocator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicParallel

open PublicSegments PublicEndpoints PublicRelative Crossing Packing Packing.Names Epoch Catalog Cover
open PreparedBins PackMotions
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

universe u
variable {B X : Type*} [Fintype B] [Fintype X] {copies V E w : ℕ}

/-- Compile the parallel child frames and the pointer-offset circuit with one
copy of each child gate list. The semantics preserve every input bit of the
merge, including opaque site data outside the geometric field selection. -/
theorem children_frames (child : Fin copies → Frame X (Raw B V E w w)) :
    ∃ (merge : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w))
      (out : Frame X (Raw B (copies*V) (copies*E) w w)),
      MergeRows merge ∧ out.size ≤ 2 + (∑ i, (child i).size) + copies*E*600*(w+1)^2 ∧
      ∀ x, out.eval x = merge.eval (fun z => (child z.1).eval x z.2) := by
  obtain ⟨merge,hsize,hread⟩ := merge_frames B copies V E w
  obtain ⟨f,hs,he⟩ := exists_parallelFrames child
  let bank := f.select (fun j : Fin copies × Raw B V E w w => ⟨j.1,j.2⟩)
  refine ⟨merge,merge.subst bank,hread,?_,?_⟩
  · simp only [bank,Frame.subst_size,Frame.select_size]
    omega
  · intro x
    have hbank : bank.eval x = fun z => (child z.1).eval x z.2 := by
      funext j; simp only [bank,Frame.select_eval,he]
    funext j
    rw [Frame.subst_eval,hbank]

variable {D q lev : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} {P : Type} {bits : P → ℕ} {R : Type u}

/-- The next catalog's reader now applies to the actual parallel pack,
without any new assumption on the combined stable pointer or site arrays. -/
theorem reconstruct_children (catalog : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    (input : Fin copies → Pack D P bits R) (sites : ∀ i, (input i).layout.Site ↪ Fin V)
    (rows : ∀ i, (input i).layout.Edge ↪ Fin E) (dummy : ∀ i, Fin E → (input i).layout.Site)
    (pos : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (lev+1))
    (field : FieldBit (↥S) (Cube D) (lev+1) → B) (mask : ∀ i, (input i).layout.Edge → Bool)
    (x : Fin copies → Raw B V E w w → Bool)
    (child : ∀ i, SegmentReady S (input i).layout (sites i) (rows i) (dummy i) (pos i) field (mask i) (x i))
    (fit : copies*V ≤ 2^w) {merge : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w)}
    (ready : MergeRows merge) {reader : Frame (Raw B (copies*V) (copies*E) w w)
      (Classified B (↥catalog.types) (copies*V) (copies*E) w w)}
    (recovers : Reconstructs.{_,u} catalog enum (Nat.zero_lt_succ lev) field reader)
    (short : ∀ i e, mask i e = true → dist (pos i ((input i).layout.src e)) (pos i ((input i).layout.dst e)) ≤ 2*h) :
    let y := merge.eval (fun z => x z.1 z.2)
    ∃ L : Labels catalog input (positiveMask input pos mask) pos,
      PhysicalReads catalog enum (Nat.zero_lt_succ lev) field input (positiveMask input pos mask)
        pos L (parallelName rows) (reader.eval y) := by
  intro y
  have g := merge_ready input sites rows dummy pos field mask x child fit ready
  exact recovers input pos (fun i => (child i).valid) mask (parallelName sites) (parallelName rows)
    (parallelDummy dummy) y g.names g.payload g.charge short

variable {N : Network D P bits} {sites : N.Site ↪ Fin V} {rows : N.Edge ↪ Fin E} {dummy : Fin E → N.Site}
variable {pos : N.Site → SurfaceHost (Cube D) (lev+1)} {field : FieldBit (↥S) (Cube D) (lev+1) → B}
variable {mask : N.Edge → Bool} {x : Raw B V E w w → Bool}

omit [Fintype B] in
/-- Dense allocator order keeps the same public source bits, widths, geometry
and charge bits. A physically occupied edge is still read at its sparse ID. -/
theorem dense_ready (g : SegmentReady S N sites rows dummy pos field mask x) :
    SegmentReady S (denseLayout N rows) sites (densePublicRows N rows) dummy pos field
      (fun i => mask ((denseSlot N rows).symm i)) x := by
  refine ⟨g.valid,represents_denseLayout N sites rows dummy g.names,g.payload,?_,?_⟩
  · intro e
    exact g.charge ((denseSlot N rows).symm e)
  · intro i hi
    exact g.hole i ((densePublicRows_range N rows) ▸ hi)

end Shortening.PublicParallel

end BorderVNP
end Computability
end OAI
