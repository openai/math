import OAI.Computability.BorderVNP.ShortenEpochSewnLocality
import OAI.Computability.BorderVNP.ShortenEpochQuotientMidpoint
import OAI.Computability.BorderVNP.ShortenCombiningConcentration

/-!
# Actual midpoint support of the three classes of output cables

The input direction bins may use any geodesic midpoints of the moved cables.
The output tile names use the chosen quotient midpoints of the physical
output endpoints. The proof therefore also covers nonunique geodesics in a
quotient. Each hook is compared to its own original lifted endpoint.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.CombiningStep

open Crossing Epoch Cover SeedIntervals Finset
open scoped Classical

variable {D m d : ℕ} [NeZero D] {K : Type*} [Field K]
    {P : Type*} {bits : P → ℕ} {I B : Type} [Fintype I] [Fintype B]

variable (p : Pack D P bits K) (bin : p.layout.Edge → Option (((I → Deck (d+1)) × B)))
    (perm : Fin D → Equiv.Perm (((I → Deck (d+1)) × B))) (e : PaidIdentity K D m)
    (positive : p.layout.Edge → Bool) (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1)))
    (q : Counts e p bin perm)

/-- Genuine quotient midpoint of a physical sewn output cable. -/
noncomputable def Placement.outputMidpoint (x : (physical p bin perm e positive q).Edge) :=
  let N := physical p bin perm e positive q
  let s := g.postSites p bin perm e positive q
  surfaceMidpoint (s (N.src x)) (s (N.dst x))

/-- The actual midpoints of new hooks and internal profile cables are at
bounded distance from the common seed center. -/
theorem Placement.new_midpoints_near_center {h ν : ℝ} (hν : 0 ≤ ν) (fits : g.fits p bin perm positive h ν) :
    let t := partition p.layout bin perm m
    let G := seedNetwork e _ (p := pieces (m := m) p bin perm) t (bundle p.layout bin perm m positive) q
    (∀ a (k : (layout p.layout bin perm m).CutPorts (t.part a)),
      dist (g.outputMidpoint p bin perm e positive q (.inl (t.includePort a k)))
        (g.project a (g.chart a).center) ≤ 2*h + ν/8*h) ∧
    ∀ a (x : (G a).Edge), dist (g.outputMidpoint p bin perm e positive q (.inr (.inr ⟨a,x⟩)))
      (g.project a (g.chart a).center) ≤ 2*h := by
  let t := partition p.layout bin perm m
  let G := seedNetwork e _ (p := pieces (m := m) p bin perm) t (bundle p.layout bin perm m positive) q
  let N := physical p bin perm e positive q
  let pos := g.postSites p bin perm e positive q
  let mid := g.outputMidpoint p bin perm e positive q
  let site (a : ((I → Deck (d+1)) × B)) (v : (G a).Site) := g.project a ((g.chart a).atSite ((G a).position v))
  have halves (x : N.Edge) : dist (mid x) (pos (N.src x)) = dist (pos (N.src x)) (pos (N.dst x)) / 2 ∧
      dist (mid x) (pos (N.dst x)) = dist (pos (N.src x)) (pos (N.dst x)) / 2 := surfaceMidpoint_dist _ _
  constructor
  · intro a k
    let x : N.Edge := .inl (t.includePort a k)
    have hs : pos (N.src x) = g.project a (g.lift a k) := by rw [g.projects]; cases k <;> rfl
    have hd : pos (N.dst x) = site a ((G a).attach k) := by
      change t.parallelSites G site ((t.parallel G).attach (t.includePort a k)) = _
      exact congrArg (t.parallelSites G site) (t.attach_include G a k)
    have hm := (halves x).2
    rw [hs,hd,dist_comm (g.project a (g.lift a k))] at hm
    have hd0 := (g.chart a).hook_midpoint_distance (fits.1 a).1 (g.project a) (g.nonexpanding a) _
      ((G a).in_ball ((G a).attach k)) _ _ (fits.2 a k) hm.le
    have hν8 : 0 ≤ ν/8 := by positivity
    have hh := mul_le_mul_of_nonneg_left (fits.1 a).2 hν8
    linarith only [hd0,(fits.1 a).2,hh]
  · intro a x
    let y : N.Edge := .inr (.inr ⟨a,x⟩)
    have hd0 := (g.chart a).internal_midpoint_distance (fits.1 a).1 (g.project a) (g.nonexpanding a)
      _ _ ((G a).in_ball ((G a).src x)) ((G a).in_ball ((G a).dst x)) (halves y).1.le
    linarith only [hd0,(fits.1 a).2]

/-- All three midpoint support implications required by the second row of
(6.3) follow from the chart fit and the actual tile addresses of input
midpoints and seed centers. The neighborhood sizes are uniform in the depth. -/
theorem physical_midpoint_support (h ν : ℝ) (hh : 0 ≤ h) (hν : 0 ≤ ν) :
    ∃ M : ℕ, ∀ d, ∃ near : (I → Deck (d+1)) → Finset (((I → Deck (d+1)) × B)),
      (∀ o, (near o).card ≤ M * Fintype.card B) ∧
      (∀ a, (univ.filter fun o => a ∈ near o).card ≤ M) ∧
      ∀ {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
        (bin : p.layout.Edge → Option (((I → Deck (d+1)) × B))) (perm : Fin D → Equiv.Perm (((I → Deck (d+1)) × B)))
        (positive : p.layout.Edge → Bool) (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1))),
      g.fits p bin perm positive h ν →
      ∀ (oldMid : p.layout.Edge → SurfaceHost I (d+1)) (addr : p.layout.Edge → ((I → Deck (d+1)) × B)),
      (∀ c a, bin c = some a → addr c = a ∧ a.1 = productTileName d (oldMid c) ∧
        dist (oldMid c) (g.old (p.layout.src c)) ≤ dist (g.old (p.layout.src c)) (g.old (p.layout.dst c))/2) →
      (∀ a, (perm 0 a).1 = productTileName d (g.project a (g.chart a).center)) →
      ∀ q : Counts e p bin perm,
      let t := partition p.layout bin perm m
      let tile := fun x => productTileName d (g.outputMidpoint p bin perm e positive q x)
      (∀ o (c : {c : (layout p.layout bin perm m).Edge // c ∉ t.selected}),
        g.inTile p bin perm e positive q tile o (.inr (.inl c)) → addr c.val.1 ∈ near o) ∧
      (∀ o a k, g.inTile p bin perm e positive q tile o (.inl (t.includePort a k)) → perm 0 a ∈ near o) ∧
      ∀ o a x, g.inTile p bin perm e positive q tile o (.inr (.inr ⟨a,x⟩)) → perm 0 a ∈ near o := by
  obtain ⟨M,hM⟩ := quotient_seed_neighbors (I := I) (B := B) (2*h + ν/8*h)
  refine ⟨M,?_⟩
  intro d
  obtain ⟨near,hin,hout,hmem⟩ := hM d
  refine ⟨near,hin,hout,?_⟩
  intro P bits p bin perm positive g fits oldMid addr hbin hctr q t tile
  have hr : 0 ≤ ν/8*h := by positivity
  let mid := g.outputMidpoint p bin perm e positive q
  have seed (a : ((I → Deck (d+1)) × B)) (x : (physical p bin perm e positive q).Edge)
      (hd : dist (mid x) (g.project a (g.chart a).center) ≤ 2*h + ν/8*h) :
      perm 0 a ∈ near (tile x) := by
    have H := hmem _ _ ((dist_comm _ _).le.trans hd) (perm 0 a).2
    rw [←hctr a] at H
    exact H
  have hdist := g.new_midpoints_near_center p bin perm e positive q hν fits
  constructor
  · intro o c hc
    obtain ⟨hc,_,rfl⟩ := hc
    have hact : (bin c.val.1).isSome = true := hc
    obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hact
    obtain ⟨he,ht,hd⟩ := hbin _ _ ha
    let x : (physical p bin perm e positive q).Edge := .inr (.inl c)
    have hm : dist (mid x) (g.old (p.layout.src c.val.1)) =
        dist (g.old (p.layout.src c.val.1)) (g.old (p.layout.dst c.val.1))/2 := (surfaceMidpoint_dist _ _).1
    have htri := dist_triangle (oldMid c.val.1) (g.old (p.layout.src c.val.1)) (mid x)
    rw [dist_comm (g.old (p.layout.src c.val.1)) (mid x),hm] at htri
    have hclose : dist (oldMid c.val.1) (mid x) ≤ 2*h + ν/8*h := by
      linarith only [htri,hd,g.bin_length _ _ ha,(fits.1 a).2,hr]
    have H := hmem _ _ hclose a.2
    rw [← ht] at H
    simpa only [he] using H
  · constructor
    · intro o a k hc
      rw [←hc.2.2]; exact seed _ _ (hdist.1 a k)
    · intro o a x hc
      rw [←hc.2.2]; exact seed _ _ ((hdist.2 a x).trans (by linarith only [hr]))

end Shortening.CombiningStep

end BorderVNP
end Computability
end OAI
