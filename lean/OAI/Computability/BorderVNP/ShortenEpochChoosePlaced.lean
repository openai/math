import OAI.Computability.BorderVNP.ShortenCubeEnumeration
import OAI.Computability.BorderVNP.ShortenEpochPlacedVariance
import OAI.Computability.BorderVNP.ShortenPreparedChildren

/-! # One joint motion choice for the actual child packs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Cover Cover.Frame Crossing Epoch Framed Hecke PackMotions Packing
open scoped Classical BorderVNP.Epoch.Cube


variable {D : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)

/-- Transporting a chosen source midpoint to an equal level leaves the
measured tile concentration equal to that of the original placed pack. -/
theorem cast_active_midpoint_concentration {d l : ℕ} (hl : d+1 = l) (hlpos : 0 < l)
    {P : Type} {bits : P → ℕ} {K : Type*} (p : PlacedPack D P bits K (Cube D) d) :
    tileConcentration (tileMass (fun c : {c : p.pack.layout.Edge // p.active c = true} =>
      fun k => addressAt l hlpos (levelCast hl (p.midpoint c.val) k)) (fun c => (p.pack.layout.width c.val : ℝ))) =
      p.concentration := by
  subst l
  exact p.active_midpoint_concentration p.active p.active_iff

/-- The variance radius used to choose independent whole-pack motions is a
uniform constant times the actual stored midpoint norm of each child. -/
theorem child_sample_energy (n : ℕ) :
    ∃ N : ℕ, ∀ d {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
      (child : Fin copies → PlacedPack D P bits K (Cube D) ((d+1)+2*n))
      (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites (d := d+1) (n := n) child)),
      (∀ i (c : (child i).pack.layout.Edge), (child i).active c = true →
        dist ((child i).midpoint c) ((child i).site ((child i).pack.layout.src c)) ≤
          dist ((child i).site ((child i).pack.layout.src c)) ((child i).site ((child i).pack.layout.dst c))/2) →
      ∀ i (s : PackSample (lattice 1) elliptic (Cube D) (d+2) n),
      (Fintype.card (Cube D → Deck (d+2)) : ℝ) * binEnergy (fun a =>
        (SeedIntervals.count (child i).pack.layout
          (B.tag (d := d+2) (n := n) (fun j => (child j).pack) (fun j => (child j).active) L.kind L.lift i s) a : ℝ)) ≤
        ((N:ℝ)*(child i).concentration)^2 := by
  obtain ⟨N,H⟩ := B.tracked_sample_energy n
  refine ⟨N,?_⟩
  intro d copies P bits K child L hm i s
  let input := fun i => (child i).pack
  let act := fun i => (child i).active
  let eq := Nat.add_right_comm (d+1) (2*n) 1
  let tracked (w : Active input act) := levelCast eq ((child w.1).midpoint w.2.val)
  have ht (w : Active input act) : dist (tracked w) (childSites (d := d+1) (n := n) child w.1
      ((input w.1).layout.src w.2.val)) ≤
      dist (childSites (d := d+1) (n := n) child w.1 ((input w.1).layout.src w.2.val))
      (childSites (d := d+1) (n := n) child w.1 ((input w.1).layout.dst w.2.val))/2 := by
    simpa only [tracked,childSites,levelCast_dist] using hm w.1 w.2.val w.2.property
  have HB := H d input act (childSites (d := d+1) (n := n) child) L tracked ht i s
  exact HB.trans_eq (congrArg (fun z : ℝ => ((N:ℝ)*z)^2)
    (cast_active_midpoint_concentration eq (by omega) (child i)))

/-- There is one physical sample for each entire child that satisfies the
scaled bin deviation of (6.2). The old child midpoint norms alone determine
the error, after fixing the word depth and the prepared catalog. -/
theorem choose_child_samples (n : ℕ) :
    ∃ N : ℕ, ∀ d {copies : ℕ} [NeZero copies] {P : Type} {bits : P → ℕ} {K : Type*}
      (child : Fin copies → PlacedPack D P bits K (Cube D) ((d+1)+2*n))
      (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites (d := d+1) (n := n) child)),
      (∀ i (c : (child i).pack.layout.Edge), (child i).active c = true →
        dist ((child i).midpoint c) ((child i).site ((child i).pack.layout.src c)) ≤
          dist ((child i).site ((child i).pack.layout.src c)) ((child i).site ((child i).pack.layout.dst c))/2) →
      ∀ X ≥ (0:ℝ), (∀ i, (child i).concentration ≤ X) →
      let input := fun i => (child i).pack
      let moved := B.tag (d := d+2) (n := n) input (fun i => (child i).active) L.kind L.lift
      ∃ ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (d+2) n,
        Real.sqrt (Fintype.card (Cube D → Deck (d+2))) *
          Real.sqrt (binEnergy (fun a => SeedIntervals.count (parallelPacks input).layout (jointBin input moved ω) a / copies -
            binMean input moved (sampleProb (d+2) n) a)) ≤ ((N:ℝ)*X)/Real.sqrt copies := by
  obtain ⟨N,H⟩ := B.child_sample_energy n
  refine ⟨N,?_⟩
  intro d copies _ P bits K child L hm X hX hc input moved
  apply choose_motions input moved (sampleProb (d+2) n)
    (fun i s => ((sampleProb_probability (d+2) n i).1 s).le) (fun i => (sampleProb_probability _ _ i).2)
    (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hX)
  intro i s
  exact (H d child L hm i s).trans (pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg N) (child i).nonneg.2) (mul_le_mul_of_nonneg_left (hc i) (Nat.cast_nonneg N)) 2)

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
