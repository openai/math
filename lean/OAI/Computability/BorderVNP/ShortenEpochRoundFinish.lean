import OAI.Computability.BorderVNP.ShortenEpochRoundWires
import OAI.Computability.BorderVNP.ShortenEpochRoundRecords

/-!
# Final motion and site realization of an actual pack

The length-to-site coefficient is fixed before the finite length alphabet.
The site budget is chosen before that alphabet as well. All bounds on width,
incidence, and retained public or expanded records refer to the same motion
and to the same algebraic pack, including its unchanged coefficient tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch.Round

open BorderVNP.Cover BorderVNP.Cover.Frame BorderVNP.Shortening BorderVNP.Crossing Finset
open scoped Classical

/-- The final physical site realization. Its type pins the underlying tensor to the given
input segment pack. The level loss and all concentration and record factors are uniform
over cover depth and network size. -/
theorem final_site_rounding :
    ∃ C ≥ (0:ℝ), ∀ (I : Type) [Fintype I] (h : ℝ), ∃ L > (0:ℝ),
    (∀ s : I → gamma 1, s ≠ 1 → (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) → s ∈ allowedMoves I L) ∧
    ∀ {T : Type} [Fintype T] (r : T → ℝ), (∀ j, 0 ≤ r j) → (∀ j, 4*r j ≤ 1) → (∀ j, r j ≤ h) →
    ∃ (a m N H : ℕ) (u : Fin m → SL) (hu : ∀ i, Clears (u i) a),
    ∀ d {D : ℕ} {P R : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits R)
      (pos : p.layout.Site → SurfaceHost I (d+2+2*a)) (ch : p.layout.Edge → Bool)
      (tag : Wires p ch → T),
      (∀ e : Wires p ch, dist (pos (p.layout.src e.val)) (pos (p.layout.dst e.val)) = r (tag e)) →
    ∃ (σ : I → Fin m) (s : SiteRoutes p I (d+1) L),
      let moved (v : p.layout.Site) := productMotion (d+2) (Equiv.refl _) (fun k => hu (σ k)) (pos v)
      (∀ v k, s.site v k = roundedSite (d+1) (moved v k)) ∧
      (∀ e, s.active e ↔ ch e ∧ productAddress (d+1) (moved (p.layout.src e)) ≠
        productAddress (d+1) (moved (p.layout.dst e))) ∧
      s.nonlocalWidth ≤ Fintype.card I*C*chargedLength p.layout pos ch ∧
      s.incidenceConcentration ≤ 2*N*tileConcentration (midpointMass (by omega) pos ch) ∧
      ∀ (ex : Bool) (prior payload : p.layout.Site → ℕ) (M : ℕ),
        (∀ t, localRecords p.layout ex prior payload (fun v => (fun k =>
          addressAt (d+2+2*a) (by omega) (pos v k)) = t) ≤ M) →
        ∀ t, localRecords p.layout ex prior payload (fun v => reduceMove (d+1) (s.origin v) = t) ≤ H*M := by
  classical
  obtain ⟨C,hC,hchoose⟩ := finite_site_rounding_bounds
  refine ⟨C,hC,?_⟩
  intro I _ h
  obtain ⟨L,hL,hgen,hroutes⟩ := rounded_site_routes (I := I) h
  refine ⟨L,hL,hgen,?_⟩
  intro T _ r hr h4 hlen
  obtain ⟨a,m,u,hu,hn⟩ := hchoose r hr h4
  obtain ⟨N,select⟩ := hn (I := I) (max h 0)
  obtain ⟨H,hload⟩ := final_round_record_bounds a I
  refine ⟨a,m,N,H,u,hu,?_⟩
  intro d D P R _ bits p pos ch tag he
  let w (e : Wires p ch) := (p.layout.width e.val : ℝ)
  let center (e : Wires p ch) := surfaceMidpoint (pos (p.layout.src e.val)) (pos (p.layout.dst e.val))
  let ends (b : Wires p ch × Bool) := pos (endAt p.layout b.1.val b.2)
  have hab (e : Wires p ch) (k : I) : dist (ends (e,false) k) (ends (e,true) k) ≤ r (tag e) :=
    (PiLp.dist_apply_le _ _ k).trans_eq (he e)
  have hne (b : Wires p ch × Bool) (k : I) : dist (center b.1 k) (ends b k) ≤ max h 0 := by
    apply (PiLp.dist_apply_le (center b.1) (ends b) k).trans
    obtain ⟨e,t⟩ := b
    have hh := hlen (tag e)
    have hm := surfaceMidpoint_dist (pos (p.layout.src e.val)) (pos (p.layout.dst e.val))
    rw [he e] at hm
    cases t
    · change dist _ (pos (p.layout.src e.val)) ≤ _
      rw [hm.1]; linarith [hr (tag e),le_max_left h 0]
    · change dist _ (pos (p.layout.dst e.val)) ≤ _
      rw [hm.2]; linarith [hr (tag e),le_max_left h 0]
  obtain ⟨σ,hwidth,hinc⟩ := select d tag w (fun _ => Nat.cast_nonneg _) (fun e k => center e k)
    (fun b k => ends b k) hab hne
  let moved (v : p.layout.Site) := productMotion (d+2) (Equiv.refl _) (fun k => hu (σ k)) (pos v)
  have hshort (e : p.layout.Edge) (hc : ch e) : dist (moved (p.layout.src e)) (moved (p.layout.dst e)) ≤ h :=
    (productMotion_dist_le _ _ _ _ _).trans ((he ⟨e,hc⟩).le.trans (hlen (tag ⟨e,hc⟩)))
  obtain ⟨s,hs,hc,hsites⟩ := hroutes p moved ch hshort
  obtain ⟨hb,hx⟩ := final_wire_identities moved ch s hs hc
  refine ⟨σ,s,hsites,hc,?_,?_,?_⟩
  · rw [hb,← length_as_sum pos ch]
    simpa [← he,w,ends,endAt,moved,productMotion] using hwidth
  · unfold SiteRoutes.incidenceConcentration
    rw [hx]
    convert! hinc using 1
  · intro ex prior payload M hM t
    simp only [hs]
    have hz := hload d (fun k => u (σ k)) (fun k => hu (σ k)) p.layout pos prior payload ex M hM t
    simp only [surfaceAddress_roundedSite] at hz
    convert! hz using 2

end Epoch.Round

end BorderVNP
end Computability
end OAI
