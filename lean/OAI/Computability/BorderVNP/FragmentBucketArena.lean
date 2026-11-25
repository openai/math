import OAI.Computability.BorderVNP.FragmentRowsPublishedRoom
import OAI.Computability.BorderVNP.FragmentRowsProgram
import OAI.Computability.BorderVNP.FragmentBucketHeader

/-! # Stable fragment bucket bounds and native control readback

The bucketer reads the populated count produced by the three native scans.
Its other operands refer to disjoint length-only reservations, which are
published by the same control vector as the fragment emitter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentArena

open Diagonal.ExternalSew.Fragments FragmentRows Packing.BottomReports.Writer

/-- The physical bucket view after the emitter sets the occupied count. -/
def Layout.bucket (l : Layout) (occupied : ℕ) : FragmentBucket.Layout :=
  ⟨l.quads,occupied,l.cells,l.pairs,l.triples,l.cursors⟩

/-- The allocated capacity separates all four regions for every possible
occupied count, including the empty stream. -/
theorem Layout.bucket_fits (l : Layout) {w n : ℕ} (bound : n≤2*l.cables+l.deliveries)
    (word : l.limit<2^w) : (l.bucket n).Fits w := by
  have cap : n < l.capacity := by unfold capacity; omega
  have term := l.footprint
  have literal : 4<2^w := by
    have : 1≤l.capacity := by unfold capacity; omega
    omega
  have after : l.cursors+l.cells ≤ l.limit := by dsimp only [limit,counts,external]; omega
  have qt : l.quads+4*n ≤ l.pairs := by dsimp only [pairs]; omega
  have pt : l.pairs+2*l.cells ≤ l.triples := by rfl
  have tc : l.triples+3*n ≤ l.cursors := by dsimp only [cursors]; omega
  refine ⟨literal,?_,?_,?_,?_,?_,after.trans word.le,Or.inl qt,Or.inl ?_,Or.inl ?_,
    Or.inl pt,Or.inl ?_,Or.inl tc⟩ <;> dsimp only [bucket] <;> omega

/-- Words below the quads survive the emitter except for its single
publication at control word 29. -/
theorem image_below (f : FragmentRows.Layout) (m : ℕ → ℕ) (z : ℕ)
    (lo : z<f.quads) (ne : z≠f.control+29) : f.image m z=m z := by
  rw [FragmentRows.Layout.image,Function.update_of_ne ne,write_outside _ _ _ _ (Or.inl lo)]

/-- The native post-emitter bucket takes its count from the true compact
stream and its addresses from the preserved fixed allocation controls. -/
theorem bucket_after_emitter (a : SignedTaskArena.Layout) (m : ℕ → ℕ) {head ctl w u v k : ℕ}
    (ptr : m (head+92)=ctl) (words : ∀ i : Fin 37, m (ctl+i.val) = a.controls i.val)
    (low : head+112≤ctl) (below : ctl+37 ≤ a.fragments.quads)
    (cables : (FragmentRows.Layout.fromFrame head m).host.count = a.cube.cables)
    (raw : m (head+9) ≤ a.cube.maxRows) (high : a.endAddress w u v k < 2^w) :
    let f := FragmentRows.Layout.fromFrame head m
    let b := a.fragments.bucket (f.stream m).length
    b.Fits w ∧ b.Header head ctl (f.image m) ∧ head+92<2^w ∧ ctl+33<2^w := by
  intro f b
  have control : f.control=ctl := ptr
  have quad : f.quads=a.fragments.quads := by
    change m (m (head+92)+28)=_
    rw [ptr]
    exact (words (28 : Fin 37)).trans rfl
  have room := (fragment_limit_le a w u v k).trans_lt high
  have total : (f.stream m).length ≤ 2*f.host.count+f.count := by
    simpa only [FragmentRows.Layout.stream,List.length_map,List.length_range] using
      stream_length f.host m (fun c => m (f.supplied+c)) ((List.range f.count).map (f.row m))
  have cableCount : f.host.count = a.cube.cables := cables
  have cnt : f.count≤a.cube.maxRows := raw
  have real : b.Fits w := a.fragments.bucket_fits (by change _ ≤ 2*a.cube.cables+a.cube.maxRows; omega) room
  have keep (i : Fin 37) (h : i.val≠29) : f.image m (ctl+i.val) = a.controls i.val := by
    rw [image_below,words]
    · have hi := i.isLt; omega
    · omega
  have point : f.image m (head+92) = ctl := by rw [image_below,ptr] <;> omega
  have num : f.image m (ctl+29)=(f.stream m).length := control ▸ f.image_count m
  have ord := FragmentRows.arena_order a
  refine ⟨real,⟨point,(keep 28 (by decide)).trans rfl,num,(keep 30 (by decide)).trans rfl,
    (keep 31 (by decide)).trans rfl,(keep 32 (by decide)).trans rfl,(keep 33 (by decide)).trans rfl⟩,?_,?_⟩ <;> omega

end RoutingISA.FragmentArena

end BorderVNP
end Computability
end OAI
