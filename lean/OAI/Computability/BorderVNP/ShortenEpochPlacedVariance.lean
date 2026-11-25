import OAI.Computability.BorderVNP.ShortenCubeEnumeration
import OAI.Computability.BorderVNP.ShortenEpochSampleVariance
import OAI.Computability.BorderVNP.ShortenPlacedStep

/-!
# Variance controlled by the tracked concentration of each child pack

A catalog template can choose a different midpoint from the stored wire
record. Both lie within half the charged length of the same endpoint. This
allows the covering-fiber bound to use the stored midpoint concentration
on the input side, with a fixed enlargement of the neighborhood.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Cover Cover.Frame Crossing Epoch Framed Finset Hecke PackMotions
open scoped Classical BorderVNP.Epoch.Cube


variable {D copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
    {I : Type} [Fintype I]

/-- The tile norm over exactly the active edge subtype is the physical pack
concentration, for any Boolean implementation of its positive charge mask. -/
theorem PlacedPack.active_midpoint_concentration {d : ℕ} (p : PlacedPack D P bits K I d)
    (active : p.pack.layout.Edge → Bool)
    (ha : ∀ c, active c = true ↔ p.charged c = true ∧ p.site (p.pack.layout.src c) ≠ p.site (p.pack.layout.dst c)) :
    tileConcentration (tileMass (fun c : {c : p.pack.layout.Edge // active c = true} =>
      fun i => addressAt (d+1) (by omega) (p.midpoint c.val i)) (fun c => (p.pack.layout.width c.val : ℝ))) =
    p.concentration := by
  classical
  have he (t : I → Deck (d+1)) :
      (∑ c : {c : p.pack.layout.Edge // active c = true},
        if productTileName d (p.midpoint c.val) = t then (p.pack.layout.width c.val : ℝ) else 0) =
      (testedWidth p.pack.layout.width (p.occupies t) : ℝ) := by
    let f (c : p.pack.layout.Edge) := if p.occupies t c then (p.pack.layout.width c : ℝ) else 0
    change _ = ((∑ c, if p.occupies t c then p.pack.layout.width c else 0 : ℕ) : ℝ)
    push_cast
    change _ = ∑ c, f c
    rw [← Fintype.sum_subtype_add_sum_subtype (fun c => active c = true) f]
    have hz : (∑ c : {c : p.pack.layout.Edge // ¬ active c = true}, f c.val) = 0 := by
      apply sum_eq_zero
      intro c _
      exact ite_eq_right (fun h => c.property ((ha c.val).mpr ⟨h.1,h.2.1⟩))
    rw [hz,add_zero]
    apply sum_congr rfl
    intro c _
    have hc := (ha c.val).mp c.property
    simp [f,PlacedPack.occupies,hc.1,hc.2]
  unfold tileConcentration PlacedPack.concentration CombiningStep.tileNorm
  congr 2
  apply congrArg binEnergy
  funext t
  exact he t

namespace PreparedBins

variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η)

/-- The catalog midpoint is within the half-length of the first actual
endpoint after quotient projection, independently of any choice of geodesic. -/
theorem Labels.midpoint_src_le {d : ℕ} (input : Fin copies → Pack D P bits K)
    (active : ∀ i, (input i).layout.Edge → Bool) (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) d)
    (L : Labels B input active sites) (w : Active input active) :
    dist (labelMidpoint (d := d) B input active L.kind L.lift w)
      (sites w.1 ((input w.1).layout.src w.2.val)) ≤ (L.kind w).val.radius := by
  let s := (L.kind w).val
  have zero : productLine s.direction 0 = productChart 0 := by
    ext1 i
    change tangentLine (unitDirection (s.direction i)) (0 * ‖s.direction i‖) = tangentChart 0
    simp [tangentLine]
  have hc : shiftTo s.center (productLine s.direction 0) = s.center := (congrArg (shiftTo s.center) zero).trans (shiftTo_chart_zero _)
  have hd : dist s.center s.ends.1 = s.radius := by
    change dist s.center (shiftTo s.center (productLine s.direction (-s.radius))) = _
    calc
      _ = dist (shiftTo s.center (productLine s.direction 0)) (shiftTo s.center (productLine s.direction (-s.radius))) :=
        congrArg (fun z => dist z _) hc.symm
      _ = _ := by rw [(shiftTo_isometry _).dist_eq, dist_productLine, zero_sub,neg_neg,abs_of_pos s.positive,s.unit,mul_one]
  rw [←L.src w]
  exact (productProjection_dist_le _ _ _).trans_eq (((translatePoint_isometry _).dist_eq _ _).trans hd)

private theorem square_refined_bound {T A : Type*} [Fintype T] [Fintype A]
    (f : A → ℝ) (g : T → ℝ) (v : ℝ) (hr : binEnergy f ≤ binEnergy g) (hg : tileConcentration g ≤ v) :
    (Fintype.card T : ℝ) * binEnergy f ≤ v^2 := by
  have h : Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy f) ≤ v :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _)).trans hg
  have hf : 0 ≤ binEnergy f := sum_nonneg fun _ _ => sq_nonneg _
  have hs := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) h 2
  rwa [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt hf] at hs

set_option maxHeartbeats 1200000 in
/-- The exact single-pack radius bound in the motion selection uses the
concentration of any actual stored midpoints of the child. Its constant
precedes the cover level, the pack family, the labels and all samples. -/
theorem tracked_sample_energy (n : ℕ) :
    ∃ N : ℕ, ∀ d {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
      (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
      (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2+2*n))
      (L : Labels B input active sites)
      (tracked : Active input active → SurfaceHost (Cube D) (d+2+2*n)),
      (∀ w : Active input active, dist (tracked w) (sites w.1 ((input w.1).layout.src w.2.val)) ≤
        dist (sites w.1 ((input w.1).layout.src w.2.val)) (sites w.1 ((input w.1).layout.dst w.2.val))/2) →
      ∀ i (s : PackSample (lattice 1) elliptic (Cube D) (d+2) n),
      (Fintype.card (Cube D → Deck (d+2)) : ℝ) *
        binEnergy (fun a => (SeedIntervals.count (input i).layout (B.tag (d := d+2) (n := n) input active L.kind L.lift i s) a : ℝ)) ≤
      ((N:ℝ) * tileConcentration (tileMass (fun x : {x : (input i).layout.Edge // active i x = true} =>
        fun k => addressAt (d+2+2*n) (by omega) (tracked ⟨i,x⟩ k)) (fun x => ((input i).layout.width x.val : ℝ))))^2 := by
  classical
  obtain ⟨N,hN⟩ := sampleMove_nearby_tile_concentration (I := Cube D) (2*h) n
  refine ⟨N,?_⟩
  intro d copies P bits K input active sites L tracked ht i s
  let E := {x : (input i).layout.Edge // active i x = true}
  let mid (x : E) := labelMidpoint (d := d+2+2*n) B input active L.kind L.lift ⟨i,x⟩
  let weight (x : E) := ((input i).layout.width x.val : ℝ)
  let measure (x : E) := tracked ⟨i,x⟩
  have hd (x : E) : dist (measure x) (mid x) ≤ 2*h := by
    let w : Active input active := ⟨i,x⟩
    have hm := L.midpoint_src_le B input active sites w
    have hs := ht w
    rw [L.length w] at hs
    have hl := B.short (L.kind w).val (L.kind w).property
    have tr := dist_triangle (tracked w) (sites i ((input i).layout.src x.val)) (mid x)
    rw [dist_comm (sites i ((input i).layout.src x.val)) (mid x)] at tr
    linarith only [hm,hs,hl,tr]
  have HL := hN d s measure mid weight (fun _ => Nat.cast_nonneg _) hd
  have HR := tag_refines_midpoints (d := d) (n := n) B input active L.kind L.lift i s
  let tag := B.tag (d := d+2) (n := n) input active L.kind L.lift i s
  let mass := tileMass (fun x : E => productTileName (d+1) (sampleMove s (mid x))) weight
  exact square_refined_bound (fun a => (SeedIntervals.count (input i).layout tag a : ℝ)) mass _ HR HL

end PreparedBins

end Shortening

end BorderVNP
end Computability
end OAI
