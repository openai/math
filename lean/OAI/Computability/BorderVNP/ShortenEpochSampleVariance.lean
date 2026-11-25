import OAI.Computability.BorderVNP.ShortenCubeEnumeration
import OAI.Computability.BorderVNP.ShortenPreparedLabels
import OAI.Computability.BorderVNP.ShortenEpochMotionEnergy

/-!
# The variance radius of the actual sampled bin counts

Splitting a tile count by relative direction, length and speed can only
decrease the sum of its squares. The absolute tile part of every sampled
active wire address equals the tile of its physically moved midpoint.
Thus the single-pack radius required by (6.2) is bounded by its old
midpoint concentration times the fixed motion-fiber constant.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Cover Cover.Frame Epoch Framed Hecke Packing PackMotions SeedIntervals Finset
open scoped Classical BorderVNP.Epoch.Cube


variable {D : ℕ} {P : Type} {bits : P → ℕ}

private theorem refined_tile_energy {T B : Type} [Fintype T] [DecidableEq T] [Fintype B]
    (N : Network D P bits) (mask : N.Edge → Bool) (tag : N.Edge → Option (T × B))
    (loc : {x : N.Edge // mask x = true} → T) (hm : ∀ x, (tag x).isSome = mask x)
    (ht : ∀ x : {x : N.Edge // mask x = true}, ∀ a, tag x.val = some a → loc x = a.1) :
    binEnergy (fun a => (count N tag a : ℝ)) ≤ binEnergy (tileMass loc (fun x => (N.width x.val : ℝ))) := by
  classical
  let f (t : T) (b : B) := (count N tag (t,b) : ℝ)
  have row (t : T) : (∑ b, f t b) = tileMass loc (fun x => (N.width x.val : ℝ)) t := by
    simp only [f,count_eq_sum,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
    rw [sum_comm]
    let g (x : N.Edge) := ∑ b : B, if tag x = some (t,b) then (N.width x : ℝ) else 0
    change ∑ x, g x = _
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x => mask x = true) g]
    have hz : (∑ x : {x : N.Edge // ¬mask x = true}, g x.val) = 0 := by
      apply sum_eq_zero
      intro x _
      have hn : tag x.val = none := by
        cases he : tag x.val with
        | none => rfl
        | some a => exact False.elim (x.property ((hm x.val).symm.trans (by simp [he])))
      simp [g,hn]
    rw [hz,add_zero]
    apply sum_congr rfl
    intro x _
    obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp ((hm x.val).trans x.property)
    rcases a with ⟨t',b'⟩
    by_cases h : t' = t <;> simp [g,ha,ht x _ ha,h]
  have hrow (t : T) : (∑ b, f t b ^ 2) ≤ (tileMass loc (fun x => (N.width x.val : ℝ)) t)^2 := by
    rw [← row,pow_two,sum_mul]
    apply sum_le_sum
    intro b _
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (single_le_sum (f := f t) (fun _ _ => Nat.cast_nonneg _) (mem_univ b))
      (Nat.cast_nonneg _)
  unfold binEnergy
  rw [Fintype.sum_prod_type]
  exact sum_le_sum fun t _ => hrow t

variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) {copies d n : ℕ} {K : Type*}
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (kind : Active input active → B.types) (lift : Active input active → Cube D → gamma 1)

/-- The particular midpoint carried by a catalogued active wire, in its source
quotient. Translating the whole lifted geodesic by the wire's common tile lift
preserves its midpoint and both oriented endpoints. -/
noncomputable def labelMidpoint (w : Active input active) : SurfaceHost (Cube D) d :=
  productProjection _ (translatePoint (lift w) (kind w).val.center)

private theorem shift_line_zero {I : Type*} (x : HyperbolicHost I) (v : PiLp 2 (fun _ : I => ℂ)) :
    shiftTo x (productLine v 0) = x := by
  refine (congrArg (shiftTo x) ?_).trans (shiftTo_chart_zero x)
  ext1 i
  change tangentLine (unitDirection (v i)) (0 * ‖v i‖) = tangentChart 0
  simp [tangentLine]

/-- The absolute component of the actual finite sample bin is exactly the
tile name of the moved midpoint, including for a center on a seam. -/
theorem sample_midpoint_tile (w : Active input active)
    (s : PackSample (lattice 1) elliptic (Cube D) (d+2) n) :
    productTileName (d+1) (sampleMove s (labelMidpoint (d := d+2+2*n) B input active kind lift w)) =
      shiftedAddress s.2.2 (movedCarry (kind w).val (lift w) s.1 s.2.1) := by
  let t := shiftedAddress s.2.2 (movedCarry (kind w).val (lift w) s.1 s.2.1)
  let conf := configuration (kind w).val (lift w) s.1 s.2.1
  have H := projects_line (kind w).val (lift w) s 0
  change sampleMove s (productProjection _ (translatePoint (lift w)
    (shiftTo (kind w).val.center (productLine (kind w).val.direction 0)))) =
    tileProject t (shiftTo conf.1 (productLine conf.2 0)) at H
  rw [shift_line_zero,shift_line_zero] at H
  exact (congrArg (productTileName (d+1)) H).trans
    (tileProject_address t conf.1 (configuration_center (kind w).val (lift w) s.1 s.2.1))

set_option maxHeartbeats 1200000 in
/-- Relative-bin counts refine the physical moved midpoint tile counts. -/
theorem tag_refines_midpoints (i : Fin copies) (s : PackSample (lattice 1) elliptic (Cube D) (d+2) n) :
    binEnergy (fun a => (count (input i).layout (B.tag (d := d+2) (n := n) input active kind lift i s) a : ℝ)) ≤
    binEnergy (tileMass (fun x : {x : (input i).layout.Edge // active i x = true} =>
      productTileName (d+1) (sampleMove s (labelMidpoint (d := d+2+2*n) B input active kind lift ⟨i,x⟩)))
      (fun x => ((input i).layout.width x.val : ℝ))) := by
  classical
  let E := {x : (input i).layout.Edge // active i x = true}
  let mid (x : E) := labelMidpoint (d := d+2+2*n) B input active kind lift ⟨i,x⟩
  let loc (x : E) := productTileName (d+1) (sampleMove s (mid x))
  let w (x : E) := ((input i).layout.width x.val : ℝ)
  let tag := B.tag (d := d+2) (n := n) input active kind lift i s
  have hm (x) : (tag x).isSome = active i x := by
    by_cases hx : active i x = true
    · simp [tag,PreparedBins.tag,sampledBin,hx]
    · simp [tag,PreparedBins.tag,sampledBin,Bool.eq_false_iff.mpr hx]
  have ht (x : E) (a) (ha : tag x.val = some a) : loc x = a.1 := by
    have hs := sample_midpoint_tile (d := d) (n := n) B input active kind lift ⟨i,x⟩ s
    have he := Option.some.inj (by simpa [tag,PreparedBins.tag,sampledBin,x.property] using ha)
    exact hs.trans (congrArg Prod.fst he)
  exact refined_tile_energy (input i).layout (active i) tag loc hm ht

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
