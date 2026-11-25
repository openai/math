import OAI.Hierarchy.TaggedWireNamedPlaces

namespace OAI
/-! # Offset of an original physical row on a shared chord -/

noncomputable section
namespace Hierarchy.WireTelescope.AggregatePrefix

open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe
open scoped Classical BigOperators

variable {n m t S : ℕ}
    (route : Fin n → List (Fin m)) (w : Fin n → ℕ)
    (ord : Fin t ≃ Σ i, Fin (route i).length) (phys : Fin m → Chord S)

/-- Every earlier original row on the same chord contributes once per routed
occurrence, with its true role width. The cutoff is the original row ordinal. -/
def paidShift (e : Fin m) :=
  ∑ u : Fin t, if (NativeSlot.edge route ord u).val < e.val ∧ phys (NativeSlot.edge route ord u) = phys e
    then w (ord u).1 else 0

private theorem sum_by_edge (keep : Fin m → Prop) :
    (∑ u : Fin t, if keep (NativeSlot.edge route ord u) then w (ord u).1 else 0) =
      ∑ i : Fin m, if keep i then routeLoad route w i else 0 := by
  let edge := NativeSlot.edge route ord
  calc
    _ = ∑ u : Fin t, ∑ i : Fin m,
        if edge u = i then (if keep i then w (ord u).1 else 0) else 0 := by simp [edge]
    _ = ∑ i : Fin m, ∑ u : Fin t,
        if edge u = i then (if keep i then w (ord u).1 else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : keep i
      · simpa only [ite_eq_left h,NativeSlot.mass,NativeSlot.amount,edge] using
          NativeSlot.mass_route route w ord i
      · simp [h]

/-- All routed occurrences on a specified chord, including parallel paid rows. -/
def chordTotal (ch : Chord S) :=
  ∑ u : Fin t, if phys (NativeSlot.edge route ord u)=ch then w (ord u).1 else 0

theorem chordTotal_eq_width (ch : Chord S) :
    chordTotal route w ord phys ch = installedWidths phys (routeLoad route w) ch := by
  calc
    _ = ∑ i : Fin m, if phys i=ch then routeLoad route w i else 0 := by
      convert sum_by_edge route w ord (fun i => phys i=ch) using 1 <;> try unfold chordTotal
      all_goals
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> rfl
    _ = _ := by
      simp [installedWidths, Finsupp.finsetSum_apply, unitChord, Finsupp.single_apply]

/-- Regroup the literal occurrences by original paid row. The resulting prefix
is exactly the native mixed-width aperture prefix, including parallel chords. -/
theorem paidShift_eq_earlier (e : Fin m) :
    paidShift route w ord phys e =
      TaggedShorterCommonScan.earlier (NamedAperture.key phys) (routeLoad route w)
        e.val (NamedAperture.key phys e) := by
  let load := routeLoad route w
  let keep := fun i : Fin m => i.val<e.val ∧ phys i=phys e
  calc
    _ = ∑ i : Fin m, if keep i then load i else 0 := by
      convert sum_by_edge route w ord keep using 1 <;> dsimp only [paidShift,keep,load]
      all_goals
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> rfl
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val<e.val), if phys i=phys e then load i else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i.val<e.val <;> simp only [keep,h,ite_true,ite_false,true_and,false_and]
    _ = _ := by
      unfold TaggedShorterCommonScan.earlier
      apply Finset.sum_bij (fun i _ => i.val)
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i _ j _ same
        exact Fin.ext same
      · intro j hj
        have bound := Finset.mem_range.mp hj
        exact ⟨⟨j,bound.trans e.isLt⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,bound⟩,rfl⟩
      · intro i _
        simp [i.isLt,NamedAperture.key,load]

/-- The whole interval fits its physical chord, even when this row width is zero. -/
theorem shift_room (e : Fin m) :
    paidShift route w ord phys e + routeLoad route w e ≤
      installedWidths phys (routeLoad route w) (phys e) := by
  let key := NamedAperture.key phys
  let load := routeLoad route w
  calc
    _ = TaggedShorterCommonScan.earlier key load (e.val+1) (key e) := by
      rw [paidShift_eq_earlier]
      exact (NativeSlot.next key load e).symm
    _ ≤ TaggedShorterCommonScan.earlier key load m (key e) :=
      NativeSlot.earlier_mono key load _ e.isLt
    _ = NativeSlot.mass key load (key e) := NativeSlot.full key load _
    _ = _ := NamedAperture.measured phys load (phys e)

/-- The mixed-radix source bit is shifted past all strictly earlier rows on
the same chord and then by its own within-row bit. -/
theorem sourceBit_val (e : Fin m) (j : Fin (routeLoad route w e)) :
    (NamedAperture.sourceBit phys (routeLoad route w) ⟨e,j⟩).val = paidShift route w ord phys e + j.val := by
  rw [paidShift_eq_earlier]
  exact NamedAperture.offset phys (routeLoad route w) ⟨e,j⟩

end Hierarchy.WireTelescope.AggregatePrefix

end
end OAI
