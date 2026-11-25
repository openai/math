import OAI.Computability.BorderVNP.ShortenEpochTerminalLoads

/-!
# Integer width minimization for the terminal motion

A finite table is calibrated from the allowed lengths. Minimizing the sum
of widths of charged cables whose moved addresses differ attains the width
estimate. The other estimates apply to every candidate in this table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch.Round

open Cover Cover.Frame Shortening Crossing Finset
open scoped Classical

variable {I : Type} [Fintype I] {D : ℕ} {P R : Type*} {bits : P → ℕ}

/-- Nonlocal integer width, calculated from the two tile names of each old cable. -/
noncomputable def terminalScore (p : Pack D P bits R) {d : ℕ}
    (moved : p.layout.Site → SurfaceHost I (d+1)) (ch : p.layout.Edge → Bool) : ℕ :=
  ∑ e, if ch e ∧ productAddress d (moved (p.layout.src e)) ≠
    productAddress d (moved (p.layout.dst e)) then p.layout.width e else 0

/-- The integer objective sums the same moved widths as the geometric averaging estimate. -/
theorem score_as_sum (p : Pack D P bits R) {d : ℕ}
    (moved : p.layout.Site → SurfaceHost I (d+1)) (ch : p.layout.Edge → Bool) :
    (terminalScore p moved ch : ℝ) = ∑ e : Wires p ch, (p.layout.width e.val : ℝ)*
      coordinateRoundingFailure d (fun i => moved (p.layout.src e.val) i)
        (fun i => moved (p.layout.dst e.val) i) := by
  let f (e : p.layout.Edge) : ℝ := if ch e ∧ productAddress d (moved (p.layout.src e)) ≠
    productAddress d (moved (p.layout.dst e)) then p.layout.width e else 0
  have hsum : (terminalScore p moved ch : ℝ) = ∑ e, f e := by
    simp only [terminalScore,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,f]
  rw [hsum,← Fintype.sum_subtype_add_sum_subtype (fun e => ch e = true) f]
  have hn : (∑ e : {e // ¬ch e = true}, f e.val) = 0 := sum_eq_zero (fun e _ => by simp [f,e.property])
  rw [hn,add_zero]
  apply sum_congr rfl
  intro e _
  rw [failure_address]
  by_cases h : productAddress d (moved (p.layout.src e.val)) = productAddress d (moved (p.layout.dst e.val))
  · simp [f,e.property,h]
  · simp [f,e.property,h]

/-- The fixed length-dependent table supports any global minimizer of the rounded
integer width. Tile labels and charge bits refer to the same minimizing candidate. -/
theorem final_site_minimum :
    ∃ C ≥ (0:ℝ), ∀ (I : Type) [Fintype I] (h : ℝ), ∃ L > (0:ℝ),
    (∀ s : I → gamma 1, s ≠ 1 → (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) → s ∈ allowedMoves I L) ∧
    ∀ {T : Type} [Fintype T] (r : T → ℝ), (∀ j, 0 ≤ r j) → (∀ j, 4*r j ≤ 1) → (∀ j, r j ≤ h) →
    ∃ (a m N H : ℕ) (u : Fin m → SL) (hu : ∀ i, Clears (u i) a), Nonempty (I → Fin m) ∧
    ∀ d {D : ℕ} {P R : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits R)
      (pos : p.layout.Site → SurfaceHost I (d+2+2*a)) (ch : p.layout.Edge → Bool)
      (tag : Wires p ch → T),
      (∀ e : Wires p ch, dist (pos (p.layout.src e.val)) (pos (p.layout.dst e.val)) = r (tag e)) →
      let moved (τ : I → Fin m) (v : p.layout.Site) :=
        productMotion (d+2) (Equiv.refl _) (fun k => hu (τ k)) (pos v)
      ∀ σ, (∀ τ, terminalScore p (moved σ) ch ≤ terminalScore p (moved τ) ch) →
      ∃ s : SiteRoutes p I (d+1) L,
      (∀ v, reduceMove (d+1) (s.origin v) = productAddress (d+1) (moved σ v)) ∧
      (∀ e, s.active e ↔ ch e ∧ productAddress (d+1) (moved σ (p.layout.src e)) ≠
        productAddress (d+1) (moved σ (p.layout.dst e))) ∧
      s.nonlocalWidth ≤ Fintype.card I*C*chargedLength p.layout pos ch ∧
      s.incidenceConcentration ≤ 2*N*tileConcentration (midpointMass (by omega) pos ch) ∧
      ∀ (ex : Bool) (prior payload : p.layout.Site → ℕ) (M : ℕ),
        (∀ t, localRecords p.layout ex prior payload (fun v => (fun k =>
          addressAt (d+2+2*a) (by omega) (pos v k)) = t) ≤ M) →
        ∀ t, localRecords p.layout ex prior payload (fun v => reduceMove (d+1) (s.origin v) = t) ≤ H*M := by
  obtain ⟨C,hC,hchoose⟩ := finite_site_rounding_bounds
  refine ⟨C,hC,?_⟩
  intro I _ h
  obtain ⟨L,hL,hgen,hroutes⟩ := rounded_site_routes (I := I) h
  refine ⟨L,hL,hgen,?_⟩
  intro T _ r hr h4 hlen
  obtain ⟨a,m,u,hu,hn⟩ := hchoose r hr h4
  obtain ⟨_,select⟩ := hn (I := I) (max h 0)
  obtain ⟨N,hinc⟩ := all_motion_loads I (max h 0) a
  obtain ⟨H,hload⟩ := final_round_record_bounds a I
  have hn : Nonempty (I → Fin m) := by
    obtain ⟨σ,_⟩ := select 0 (W := Empty) Empty.elim (fun _ => 0) (fun _ => le_rfl)
      Empty.elim (fun b => b.1.elim) (fun j => nomatch j) (fun b => nomatch b.1)
    exact ⟨σ⟩
  refine ⟨a,m,N,H,u,hu,hn,?_⟩
  intro d D P R _ bits p pos ch tag he moved σ hmin
  let w (e : Wires p ch) := (p.layout.width e.val : ℝ)
  let center (e : Wires p ch) := surfaceMidpoint (pos (p.layout.src e.val)) (pos (p.layout.dst e.val))
  let ends (b : Wires p ch × Bool) := pos (endAt p.layout b.1.val b.2)
  have hab (e : Wires p ch) (k : I) : dist (ends (e,false) k) (ends (e,true) k) ≤ r (tag e) :=
    (PiLp.dist_apply_le _ _ k).trans_eq (he e)
  have hnear (b : Wires p ch × Bool) (k : I) : dist (center b.1 k) (ends b k) ≤ max h 0 := by
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
  obtain ⟨τ,hw,_⟩ := select d tag w (fun _ => Nat.cast_nonneg _) (fun e k => center e k)
    (fun b k => ends b k) hab hnear
  have hshort (e : p.layout.Edge) (hc : ch e) : dist (moved σ (p.layout.src e)) (moved σ (p.layout.dst e)) ≤ h :=
    (productMotion_dist_le _ _ _ _ _).trans ((he ⟨e,hc⟩).le.trans (hlen (tag ⟨e,hc⟩)))
  obtain ⟨s,hs,hc,_⟩ := hroutes p (moved σ) ch hshort
  obtain ⟨hb,hx⟩ := final_wire_identities (moved σ) ch s hs hc
  let keep (e : Wires p ch) := w e * coordinateRoundingFailure (d+1)
    (fun k => moved σ (p.layout.src e.val) k) (fun k => moved σ (p.layout.dst e.val) k)
  have hkeep (e : Wires p ch) : 0 ≤ keep e ∧ keep e ≤ w e := by
    dsimp only [keep]; rw [failure_address]
    split <;> simp [w]
  have hi := hinc d (fun k => u (σ k)) (fun k => hu (σ k)) (fun e k => center e k)
    (fun b k => ends b k) w keep (fun _ => Nat.cast_nonneg _) hkeep hnear
  refine ⟨s,hs,hc,?_,?_,?_⟩
  · rw [hb,← score_as_sum p (moved σ) ch,← length_as_sum pos ch]
    have hle : (terminalScore p (moved σ) ch : ℝ) ≤ terminalScore p (moved τ) ch := by exact_mod_cast hmin τ
    apply hle.trans
    rw [score_as_sum]
    simpa only [← he,w,ends,endAt,Bool.false_eq_true,↓reduceIte,moved,productMotion,Equiv.refl_apply] using hw
  · unfold SiteRoutes.incidenceConcentration
    rw [hx]
    simp only [surfaceAddress_roundedSite]
    exact hi
  · intro ex prior payload M hM t
    simp only [hs]
    have hz := hload d (fun k => u (σ k)) (fun k => hu (σ k)) p.layout pos prior payload ex M hM t
    simp only [surfaceAddress_roundedSite] at hz
    exact hz

end Epoch.Round

end BorderVNP
end Computability
end OAI
