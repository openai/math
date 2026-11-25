import OAI.Computability.BorderVNP.PackedSiteEpochs
import OAI.Computability.BorderVNP.PackedGridSlots
import OAI.Computability.BorderVNP.PackedGridDeck

/-! # Integral site routes and potential of the initial public neighbor grid

Only the grid channels crossing between distinct physical sites are charged.
The repeated-width grid is regular, so its endpoint concentration is bounded
by twice its total possible cable width. The construction uses the integral
routing generators present in the epoch schedule.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PhysicalEpochs

open Crossing Shortening Cover Epoch Finset
open scoped Classical

variable {D q d : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}

/-- The vertex and channel numbering of a public directed Cayley grid. This
description applies also after grouping its exterior slots into intervals. -/
structure GridShape (N : Network D P bits) (q d : ℕ) where
  /-- All physical vertices, indexed by the product deck. -/
  vertex : N.Site ≃ (Fin q → Deck (d+1))
  /-- One physical cable for every site and every direction. -/
  channel : N.Edge ≃ ((Fin q → Deck (d+1)) × DeckGrid.Direction q)
  /-- The site component of the channel is its source. -/
  source : ∀ e, vertex (N.src e) = (channel e).1
  /-- The target is the source translated by the public direction letter. -/
  target : ∀ e, vertex (N.dst e) = (channel e).1 * DeckGrid.step q (d+1) (channel e).2

namespace GridShape

/-- Reindexing the deck coordinates from the finite numbered grid to the cube. -/
def coordinate (ord : Cube D ≃ Fin q) : (Fin q → Deck (d+1)) ≃ (Cube D → Deck (d+1)) :=
  ord.symm.arrowCongr (Equiv.refl _)

private noncomputable def representative (d : ℕ) (g : Deck (d+1)) : gamma 1 :=
  (QuotientGroup.mk'_surjective ((gamma (d+1)).subgroupOf (gamma 1)) g).choose

private theorem representative_eq (g : Deck (d+1)) : (representative d g : Deck (d+1)) = g :=
  (QuotientGroup.mk'_surjective ((gamma (d+1)).subgroupOf (gamma 1)) g).choose_spec

private def letter (ord : Cube D ≃ Fin q) (j : DeckGrid.Direction q) : Cube D → gamma 1 :=
  fun i => if ord i = j.1 then ⟨j.2.val,routingGenerators_mem _ j.2.property⟩ else 1

private theorem reduce_letter (ord : Cube D ≃ Fin q) (j : DeckGrid.Direction q) :
    reduceMove d (letter ord j) = coordinate ord (DeckGrid.step q (d+1) j) := by
  funext i
  by_cases hi : ord i = j.1 <;> simp [coordinate,reduceMove,letter,DeckGrid.step,productStep,hi]

variable {N : Network D P bits} (S : GridShape N q d) (ord : Cube D ≃ Fin q)
variable [Field K] (F : Factory D K) (table : N.Tables K)

/-- Integral lifts of every public grid vertex. Their reductions are the
numbered grid sites in the cube coordinate convention. -/
noncomputable def origin (v : N.Site) : Cube D → gamma 1 :=
  fun i => representative d (S.vertex v (ord i))

/-- Reducing a vertex lift recovers its exact public physical site. -/
theorem origin_reduction (v : N.Site) :
    reduceMove d (S.origin ord v) = coordinate ord (S.vertex v) :=
  funext fun i => representative_eq (S.vertex v (ord i))

/-- The actual bottom site pack for the public grid. Every nonlocal directed
cable is registered, including the padded ones with zero endpoint factors. -/
noncomputable def routesWith {L : ℝ} (allow : ∀ a : Cube D → gamma 1, a ≠ 1 →
    (∀ i, a i = 1 ∨ (a i).val ∈ routingGenerators) → a ∈ allowedMoves (Cube D) L) :
    SiteRoutes (Pack.mk N table) (Cube D) d L where
  origin := S.origin ord
  active e := decide (S.vertex (N.src e) ≠ S.vertex (N.dst e))
  step e he := by
    let j := (S.channel e).2
    refine ⟨letter ord j,allow _ ?_ ?_⟩
    · intro eq
      have red := reduce_letter (d := d) ord j
      rw [eq] at red
      have hj : DeckGrid.step q (d+1) j = 1 := by
        apply (coordinate ord).injective
        exact red.symm
      have h := of_decide_eq_true he
      apply h
      rw [S.source,S.target,show DeckGrid.step q (d+1) (S.channel e).2 = 1 from hj,mul_one]
    · intro i
      by_cases hi : ord i = j.1
      · exact Or.inr (by simp [letter,hi])
      · exact Or.inl (by simp [letter,hi])
  aligned e _ := by
    change reduceMove d (S.origin ord (N.dst e)) =
      reduceMove d (S.origin ord (N.src e)) * reduceMove d (letter ord (S.channel e).2)
    rw [S.origin_reduction,S.origin_reduction,S.source,S.target,reduce_letter]
    rfl

/-- Initial physical routes at the generator budget of this outer factory. -/
noncomputable def routes : SiteRoutes (Pack.mk N table) (Cube D) d F.L :=
  S.routesWith ord table F.generators

/-- In the actual routed grid a cable is charged precisely when it connects
distinct sites. -/
theorem active_iff (e : N.Edge) : (S.routes ord F table).active e ↔ N.src e ≠ N.dst e := by
  change decide (S.vertex (N.src e) ≠ S.vertex (N.dst e)) = true ↔ _
  simp

private theorem sum_active_le {V : Type*} [Fintype V] (act : V → Bool) (f : V → ℝ)
    (hf : ∀ e, 0 ≤ f e) : (∑ e : {e : V // act e}, f e) ≤ ∑ e : V, f e := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun e => act e = true) f]
  exact le_add_of_nonneg_right (sum_nonneg fun e _ => hf e)

omit [Field K] in
/-- With uniform width bound W, all sites have at most two ends of width W
per direction, counting both source and destination separately. -/
theorem incidence_le_of_reduction {L : ℝ} (s : SiteRoutes (Pack.mk N table) (Cube D) d L)
    (horigin : ∀ v, reduceMove d (s.origin v) = coordinate ord (S.vertex v)) {W : ℕ} (hwidth : ∀ e, N.width e ≤ W) (tile : Cube D → Deck (d+1)) :
    s.incidence tile ≤ 2 * Fintype.card (DeckGrid.Direction q) * (W : ℝ) := by
  let G := Fin q → Deck (d+1)
  let J := DeckGrid.Direction q
  let g := (coordinate ord).symm tile
  have end_le (endp : N.Edge → N.Site) (shift : J → Equiv.Perm G)
      (he : ∀ e, S.vertex (endp e) = shift (S.channel e).2 (S.channel e).1) :
      (∑ e : s.Active, if reduceMove d (s.origin (endp e.val)) = tile then (N.width e : ℝ) else 0) ≤
        Fintype.card J * (W : ℝ) := by
    let f (e : N.Edge) := if reduceMove d (s.origin (endp e)) = tile then (N.width e : ℝ) else 0
    have loc (e : N.Edge) : reduceMove d (s.origin (endp e)) = tile ↔
        shift (S.channel e).2 (S.channel e).1 = g := by
      rw [show reduceMove d (s.origin (endp e)) = coordinate ord (S.vertex (endp e)) from
        horigin _,he,← (coordinate ord).eq_symm_apply]
    calc
      _ ≤ ∑ e : N.Edge, f e := sum_active_le s.active f (fun e => by dsimp [f]; split <;> positivity)
      _ ≤ ∑ e : N.Edge, if shift (S.channel e).2 (S.channel e).1 = g then (W : ℝ) else 0 := by
        apply sum_le_sum
        intro e _
        dsimp only [f]
        by_cases h : shift (S.channel e).2 (S.channel e).1 = g
        · rw [ite_eq_left ((loc e).mpr h),ite_eq_left h]
          exact_mod_cast hwidth e
        · rw [ite_eq_right (fun eq => h ((loc e).mp eq)),ite_eq_right h]
      _ = ∑ e : G × J, if shift e.2 e.1 = g then (W : ℝ) else 0 :=
        S.channel.sum_comp (fun e => if shift e.2 e.1 = g then (W : ℝ) else 0)
      _ = _ := by
        rw [Fintype.sum_prod_type_right]
        have leg (j : J) : (∑ z : G, if shift j z = g then (W : ℝ) else 0) = W := by
          calc
            _ = ∑ z : G, if z = g then (W : ℝ) else 0 :=
              Equiv.sum_comp (shift j) (fun z => if z = g then (W : ℝ) else 0)
            _ = _ := by
              rw [sum_eq_single g]
              · exact ite_eq_left rfl
              · intro z _ hz; exact ite_eq_right hz
              · intro hg; exact False.elim (hg (mem_univ _))
        simp [leg]
  have hl := end_le N.src (fun _ => Equiv.refl G) S.source
  have hr := end_le N.dst (fun j => Equiv.mulRight (DeckGrid.step q (d+1) j)) S.target
  apply (add_le_add hl hr).trans_eq
  dsimp [J]
  ring

/-- Incidence of the grid using the schedule's chosen integral lifts. -/
theorem incidence_le {W : ℕ} (hwidth : ∀ e, N.width e ≤ W) (tile : Cube D → Deck (d+1)) :
    (S.routes ord F table).incidence tile ≤ 2 * Fintype.card (DeckGrid.Direction q) * (W : ℝ) := by
  exact S.incidence_le_of_reduction ord table _ (S.origin_reduction ord) hwidth tile

omit [Field K] in
set_option maxHeartbeats 1000000 in
/-- Nonlocal cable bits and weighted site concentration of the physical grid.
The bound includes all padded and repeated channels, independently of the
private equality/box factors installed at the vertices. -/
theorem potential_le_of_reduction {L weight : ℝ} (s : SiteRoutes (Pack.mk N table) (Cube D) d L)
    (horigin : ∀ v, reduceMove d (s.origin v) = coordinate ord (S.vertex v)) (hwgt : 0 ≤ weight)
    {W : ℕ} (hwidth : ∀ e, N.width e ≤ W) :
    s.potential weight ≤
      (1+2*weight) * CoverScale.sites (Cube D) d * Fintype.card (DeckGrid.Direction q) * (W : ℝ) := by
  let V := CoverScale.sites (Cube D) d
  let J := Fintype.card (DeckGrid.Direction q)
  let A := 2 * (J : ℝ) * W
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbits : s.nonlocalWidth ≤ (V : ℝ)*J*W := by
    have hcard : Fintype.card N.Edge = V * J := by
      rw [Fintype.card_congr S.channel,Fintype.card_prod,Fintype.card_congr (coordinate (d := d) ord)]
      exact congrArg (· * J) (card_eq_sites (Cube D) d _)
    calc
      _ ≤ ∑ _ : N.Edge, (W : ℝ) := by
        apply sum_le_sum
        intro e _
        split
        · exact_mod_cast hwidth e
        · positivity
      _ = _ := by simp [hcard,mul_assoc]
  have hinc : s.incidenceConcentration ≤ V * A := by
    have bound (tiles : Fintype (Cube D → Deck (d+1))) :
        @tileConcentration _ tiles s.incidence ≤ (V : ℝ)*A := by
      let _ := tiles
      have he : @binEnergy _ tiles s.incidence ≤ (V : ℝ)*A^2 := by
        calc
          _ ≤ ∑ _ : Cube D → Deck (d+1), A^2 := by
            apply sum_le_sum
            intro tile _
            have h0 : 0 ≤ s.incidence tile := by
              unfold SiteRoutes.incidence
              apply add_nonneg <;> apply sum_nonneg <;> intro e _ <;> split <;> positivity
            exact pow_le_pow_left₀ h0 (S.incidence_le_of_reduction ord table s horigin hwidth tile) 2
          _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,card_eq_sites (Cube D) d tiles]; rfl
      unfold tileConcentration
      rw [card_eq_sites (Cube D) d tiles]
      calc
        _ ≤ Real.sqrt V * Real.sqrt (V * A^2) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _)
        _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq hA,← mul_assoc,Real.mul_self_sqrt (Nat.cast_nonneg _)]
    exact bound _
  have hw := mul_le_mul_of_nonneg_left hinc hwgt
  change s.nonlocalWidth + weight * s.incidenceConcentration ≤ _
  dsimp only [A] at hw
  change _ ≤ (1+2*weight) * V * J * W
  linarith only [hbits,hw]


/-- Potential of the public grid in the outer epoch factory. -/
theorem potential_le {W : ℕ} (hwidth : ∀ e, N.width e ≤ W) :
    (S.routes ord F table).potential F.weight ≤
      (1+2*F.weight) * CoverScale.sites (Cube D) d * Fintype.card (DeckGrid.Direction q) * (W : ℝ) := by
  exact S.potential_le_of_reduction ord table _ (S.origin_reduction ord) F.weight_pos.le hwidth

end GridShape
end Packing.PhysicalEpochs

end BorderVNP
end Computability
end OAI
