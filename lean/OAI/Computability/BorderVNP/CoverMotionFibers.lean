import OAI.Computability.BorderVNP.CoverMotionTable

/-!
# Bounded preimages of a finite-tile placement

The locality estimate in §6 can be expressed directly in tile addresses. Fix
one relative source segment. Its output tile is the motion correction times
a displacement depending only on the fixed low residue. For the same low
residue the displacement cancels. Conjugating back by the inverse motion
then bounds the number of possible input tiles by a fixed congruence index.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

private theorem lift_card (d k l : ℕ) (hl : l = d+k) (hd : 2 ≤ d) (t : Deck d) :
    (CoverDeck.fiber (deckReduction (show d ≤ l by omega)) t).card = (7^3)^k := by
  subst l
  let π := deckReduction (show d ≤ d+k by omega)
  have hs := deckReduction_surjective (show d ≤ d+k by omega)
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := π) (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  change Finset.univ.card = ∑ v, (CoverDeck.fiber π v).card at hsum
  simp_rw [CoverDeck.fiber_card_eq_kernel π hs] at hsum
  simp only [Finset.card_univ,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,
    ← Nat.card_eq_fintype_card (α := Deck _),deck_card] at hsum
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hd
  have hg : tileCount (d+k) = (7^3)^k * tileCount d := by
    rw [show d+k = (n+k)+2 by omega,show d=n+2 by omega,tileCount_eq (n+k),tileCount_eq n,pow_add]
    ring
  have hp : 0 < tileCount d := by
    rw [show d=n+2 by omega,tileCount_eq n]
    exact Nat.mul_pos (by positivity) tileCount_two_bounds.1
  rw [hg] at hsum
  rw [CoverDeck.fiber_card_eq_kernel π hs t]
  exact Nat.mul_right_cancel hp ((mul_comm _ _).trans hsum.symm)

/-- Two representatives with the same low table entry and the same output
correction at depth `d+2*a` have the same input tile at depth `d`. -/
theorem same_depth_of_same_correction {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ)
    (x y : lattice 1) (hl : tile (1+2*a) x = tile (1+2*a) y)
    (ho : tile (d+2*a) (correction hg x) = tile (d+2*a) (correction hg y)) :
    tile d x = tile d y := by
  have hr : lowRepresentative a x = lowRepresentative a y := congrArg Quotient.out hl
  have h := conjugate_lattice hg.inv d ((tile_eq_iff _ _ _).mp ho)
  apply (tile_eq_iff _ _ _).mpr
  change g⁻¹*((g*((y:SL)*(lowRepresentative a y : SL)⁻¹)*g⁻¹) *
    (g*((x:SL)*(lowRepresentative a x : SL)⁻¹)*g⁻¹)⁻¹)*g⁻¹⁻¹ ∈ lattice d at h
  rw [hr] at h
  simpa only [show g⁻¹*((g*((y:SL)*(lowRepresentative a y : SL)⁻¹)*g⁻¹) *
    (g*((x:SL)*(lowRepresentative a y : SL)⁻¹)*g⁻¹)⁻¹)*g⁻¹⁻¹ = (y:SL)*(x:SL)⁻¹ by group] using h

/-- Output tile of one fixed relative pattern. The fixed table determines
the displacement from the correction tile. -/
noncomputable def placedTile {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d)
    (offset : Deck (1+2*a) → Deck (d+2*a)) (x : Deck (d+2*a+2*a)) : Deck (d+2*a) :=
  motionDeck hg (show 1 ≤ d+2*a by omega) x *
    offset (deckReduction (show 1+2*a ≤ d+2*a+2*a by omega) x)

private theorem coarse_of_same_placement {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d)
    (offset : Deck (1+2*a) → Deck (d+2*a)) (x y : Deck (d+2*a+2*a))
    (hl : deckReduction (show 1+2*a ≤ d+2*a+2*a by omega) x =
      deckReduction (show 1+2*a ≤ d+2*a+2*a by omega) y)
    (ho : placedTile hg hd offset x = placedTile hg hd offset y) :
    deckReduction (show d ≤ d+2*a+2*a by omega) x =
      deckReduction (show d ≤ d+2*a+2*a by omega) y := by
  unfold placedTile at ho
  rw [hl] at ho
  have he := mul_right_cancel ho
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective ((gamma _).subgroupOf (gamma 1)) x
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective ((gamma _).subgroupOf (gamma 1)) y
  have hl' := congrArg (deckTileEquiv (1+2*a)) hl
  change tile _ (baseFrame u) = tile _ (baseFrame v) at hl'
  have ho' := congrArg (deckTileEquiv (d+2*a)) he
  change deckTileEquiv _ (motionDeck hg _ (u : Deck (d+2*a+2*a))) =
    deckTileEquiv _ (motionDeck hg _ (v : Deck (d+2*a+2*a))) at ho'
  rw [motionDeck_rep,motionDeck_rep] at ho'
  exact (deckTileEquiv d).injective (same_depth_of_same_correction hg d _ _ hl' ho')

/-- The inverse-image multiplicity of a relative segment's output tile is
bounded independently of the output level. The factor `tileCount (1+2*a)`
counts low table keys, and `343^(4*a)` counts all high lifts after the
inverse-conjugation calculation. -/
theorem placedTile_fiber_bound {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 2 ≤ d)
    (offset : Deck (1+2*a) → Deck (d+2*a)) (t : Deck (d+2*a)) :
    (CoverDeck.fiber (placedTile hg (by omega) offset) t).card ≤
      tileCount (1+2*a) * (7^3)^(4*a) := by
  let P := placedTile hg (show 1 ≤ d by omega) offset
  let L := deckReduction (show 1+2*a ≤ d+2*a+2*a by omega)
  let Q := deckReduction (show d ≤ d+2*a+2*a by omega)
  let S := CoverDeck.fiber P t
  have hh (v : Deck (1+2*a)) : (S.filter (fun x => L x = v)).card ≤ (7^3)^(4*a) := by
    by_cases h : (S.filter (fun x => L x = v)).Nonempty
    · obtain ⟨x,hx⟩ := h
      have sub : S.filter (fun y => L y = v) ⊆ CoverDeck.fiber Q (Q x) := by
        intro y hy
        obtain ⟨sy,ly⟩ := Finset.mem_filter.mp hy
        obtain ⟨sx,lx⟩ := Finset.mem_filter.mp hx
        have he := coarse_of_same_placement hg (by omega) offset y x (ly.trans lx.symm)
          ((Finset.mem_filter.mp sy).2.trans (Finset.mem_filter.mp sx).2.symm)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
      refine (Finset.card_le_card sub).trans_eq ?_
      exact lift_card d (4*a) (d+2*a+2*a) (by omega) hd (Q x)
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  have hs := Finset.card_eq_sum_card_fiberwise (f := L) (s := S) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  change S.card ≤ _
  rw [hs]
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
    ← Nat.card_eq_fintype_card (α := Deck _),deck_card] using
      Finset.sum_le_sum (s := Finset.univ) (fun v _ => hh v)

end Cover.Frame

end BorderVNP
end Computability
end OAI
