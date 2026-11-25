import OAI.Computability.BorderVNP.RoutingISAEvalCoreTicks
import OAI.Computability.BorderVNP.GeometryAdviceCharge

/-! # Applying the team clock to the linked native passes

The core runs in the explicitly checked routing allowance. Public descriptors
are charged at the public-work scale plus the label/owner tables; local packet,
cell and entry work is charged at the exterior scale times a fixed polynomial
in the address length. The resulting cap has one threshold independent of
the batch size and of the contents of the directories.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open Filter TeamScales

/-- Public descriptor/geometry work at the chosen alphabet size. -/
noncomputable def publicWork (a : ℕ) (α : ℝ) (r n R : ℕ) : ℝ :=
  r*(n:ℝ)^(19/20:ℝ) + ((Routing.labelCount a α n:ℝ)+R)^10

/-- Per-team individual bit work and the finite-dimensional tables, with
their polynomial word-length overhead as in (8.3). -/
noncomputable def localWork (a D : ℕ) (α ξ : ℝ) (r n R : ℕ) : ℝ :=
  ((exterior ξ r n:ℝ) + ((Routing.labelCount a α n:ℝ)+R)^10) * (logWidth r n:ℝ)^D

/-- Once the public record and local bit counts of an evaluator have been
bounded at their respective scales, its measured core and both kinds of work
fit the actual rounded tick limit, uniformly over the stretched-exponential
range of processors. -/
theorem eventually_eval_clock (a D : ℕ) (ha : 1 ≤ a) {α ξ : ℝ} (hα : 0 ≤ α)
    (small : α*(a:ℝ)<1/10^6) (hξ : 0 < ξ) (hξ' : ξ<1/25) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∀ᶠ n : ℕ in atTop, ∀ r R N core publicSteps localSteps : ℕ, 1 ≤ r → 1 ≤ R →
        (r:ℝ) ≤ 2^((n:ℝ)^ω) → (R:ℝ) ≤ (n:ℝ)^(2*α) →
        core ≤ 2048*(exterior ξ r n+(R+1)^3+N+r+1) →
        (N:ℝ) ≤ A*publicWork a α r n R →
        (publicSteps:ℝ) ≤ B*publicWork a α r n R →
        (localSteps:ℝ) ≤ B*localWork a D α ξ r n R →
        core+publicSteps+localSteps ≤ ticks ξ r n := by
  obtain ⟨ω,hω,rate⟩ := Routing.eventually_team_ticks a D ha hα small hξ hξ'
  refine ⟨ω,hω,?_⟩
  intro A B hA hB
  let C := 2048*(11+A)+2*B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [rate C hC,eventually_ge_atTop 1] with n bound hn
  intro r R N core pubN locN hr hR batch teams hcore hrows hp hl
  let X : ℝ := exterior ξ r n
  let z : ℝ := Routing.labelCount a α n
  let g : ℝ := (z+R)^10
  let b : ℝ := r*(n:ℝ)^(19/20:ℝ)
  let p : ℝ := (logWidth r n:ℝ)^D
  let E : ℝ := b+(X+g)*p
  have npos : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have rpos : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have Rpos : 1 ≤ (R:ℝ) := by exact_mod_cast hR
  have zpos : 0 ≤ z := by dsimp [z]; positivity
  have Xpos : 0 ≤ X := by dsimp [X]; positivity
  have gpos : 0 ≤ g := by dsimp [g]; positivity
  have bR : (r:ℝ) ≤ b := by
    exact (mul_one (r:ℝ)) ▸ mul_le_mul_of_nonneg_left (Real.one_le_rpow npos (by norm_num : 0 ≤ (19/20:ℝ))) (by positivity)
  have ppos : 1 ≤ p := by
    apply one_le_pow₀
    exact_mod_cast (GeometryAdviceRate.indexWidths hr hn).1
  have gX : X+g ≤ (X+g)*p := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ppos (show 0 ≤ X+g by positivity)
  have bpos := rpos.trans bR
  have rb : (r:ℝ) ≤ E := by dsimp [E]; linarith
  have one : 1 ≤ E := rpos.trans rb
  have xb : X ≤ E := by dsimp [E]; linarith
  have gb : g ≤ E := by dsimp [E]; linarith
  have cubes : ((R:ℝ)+1)^3 ≤ 8*g := by
    have c : (R:ℝ)+1 ≤ 2*(z+R) := by linarith
    have a := pow_le_pow_left₀ (by positivity) c 3
    have hi := pow_le_pow_right₀ (show 1 ≤ z+(R:ℝ) by linarith) (show 3 ≤ 10 by decide)
    dsimp [g]
    nlinarith only [a,hi]
  have publicLe : publicWork a α r n R ≤ E := by change b+g ≤ b+(X+g)*p; linarith
  have localLe : localWork a D α ξ r n R ≤ E := by change (X+g)*p ≤ b+(X+g)*p; linarith
  have nr := hrows.trans (mul_le_mul_of_nonneg_left publicLe hA)
  have pp := hp.trans (mul_le_mul_of_nonneg_left publicLe hB)
  have ll := hl.trans (mul_le_mul_of_nonneg_left localLe hB)
  have hc : (core:ℝ) ≤ 2048*(X+((R:ℝ)+1)^3+N+r+1) := by dsimp [X]; exact_mod_cast hcore
  have finish := bound r R hr batch teams
  change C*E < (r:ℝ)*(n:ℝ)^(1-ξ/2) at finish
  apply Nat.le_floor
  push_cast
  apply le_trans _ finish.le
  dsimp only [C]
  linarith only [hc,xb,cubes,gb,nr,rb,one,pp,ll]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
