import OAI.Hierarchy.DescentRouterActorLoads
import OAI.Hierarchy.DescentRelabeledRotor
import OAI.Hierarchy.DescentActorMass

namespace OAI
/-! # Whole occupied loads for actual paid base actors and fallback terminal actors -/

namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentBaseProfile DescentMixedRouter DescentRouterSlots DescentResetTrunks
open scoped BigOperators Classical
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k n : ℕ}
variable (P : Placement V I H A k (2^n)) (u : ℕ)

set_option Elab.async false

theorem fallback_bin (s : Bool) (t : H) :
    terminalWeight u P.contact P.owner s (.inr t)≤bin (fun i=>P.fall s (P.old s i)) (fun _=>u) t := by
  let home (i : I) := P.fall s (P.old s i)
  let toHome (i : Item P.contact P.owner s (.inr t)) : DescentNamedContact.Fibre home t := by
    refine ⟨i.val, ?_⟩
    change P.fall s (P.old s i.val) = t
    have h := (P.align s i.val).trans i.property
    by_cases paid : useRotor P.b P.depth P.L P.keys P.hub P.old i.val
    · simp [Placement.site, Placement.input, DescentChosenRouter.site, pub, paid] at h
    · simpa [Placement.site, Placement.input, DescentChosenRouter.site, pub, paid] using h
  have injective : Function.Injective toHome := by
    intro a b eq
    exact Subtype.ext (congrArg (fun j : DescentNamedContact.Fibre home t => j.val) eq)
  calc
    terminalWeight u P.contact P.owner s (.inr t)
        ≤ Fintype.card (DescentNamedContact.Fibre home t) * u := by
          unfold terminalWeight
          apply Nat.mul_le_mul_right
          simp only [Fintype.card_eq_nat_card]
          exact Nat.card_le_card_of_injective toHome injective
    _ = DescentNamedContact.width home (fun _ => u) t := by
      simp only [DescentNamedContact.width, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.cast_id, Fintype.card_eq_nat_card]
    _ = _ := width_bin home (fun _ => u) t

namespace Dyadic
variable (D : Dyadic V I k) {B S : ℝ} (L : D.Loads (2^n) B S u)
variable (pos : 0<S) (pu : 0<u) (ub : (u:ℝ)≤B) (ys : ((2^n : ℕ):ℝ)*B≤S) (fall : Bool→V×Block k→H)

theorem good_items (s : Bool) (g : D.G) :
    (terminalWeight u (D.install L pos (Nat.cast_pos.mpr pu) ub ys fall).contact
      (D.install L pos (Nat.cast_pos.mpr pu) ub ys fall).owner s (.inl g):ℝ)≤2*S := by
  have hB : 0 < B := (Nat.cast_pos.mpr pu : (0 : ℝ) < u).trans_le ub
  obtain ⟨factor, rfl⟩ : ∃ f : ℝ, S = f * B :=
    ⟨S / B, (div_mul_cancel₀ S hB.ne').symm⟩
  let placed := D.install L pos (Nat.cast_pos.mpr pu) ub ys fall
  change (terminalWeight u placed.contact placed.owner s (.inl g) : ℝ) ≤ 2 * (factor * B)
  have mass : terminalWeight u placed.contact placed.owner s (.inl g) =
      Fintype.card (D.AtBase s g) * u := by
    unfold terminalWeight
    apply congrArg (fun m : ℕ => m * u)
    simp only [Fintype.card_eq_nat_card]
    exact Nat.card_congr (D.bundleEquiv (factor := factor) L pos pu ub ys fall s g).symm
  have count : Fintype.card (D.AtBase s g)=
      ∑o : D.OldAt g,(Finset.univ.filter fun z : D.AtBase s g=>D.whole s g z=o).card := by
    simpa only [Finset.card_univ] using (Finset.card_eq_sum_card_fiberwise (s:=Finset.univ) (t:=Finset.univ)
      (f:=D.whole s g) (fun _ _=>Finset.mem_univ _))
  rw [mass, count, Nat.cast_mul, Nat.cast_sum, Finset.sum_mul]
  refine le_trans ?_ (L.full s g)
  apply Finset.sum_le_sum
  intro o _
  refine (congrArg (fun f : Finset (D.AtBase s g) => (f.card : ℝ) * u) ?_).le.trans
    (L.carried s g o)
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Dyadic
end
end Hierarchy.DescentChosenRouter

end OAI
