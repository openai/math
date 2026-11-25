import OAI.Computability.BorderVNP.RoutingISAScheduleClockRuns
import OAI.Computability.BorderVNP.RoutingISAScheduleClockCube

/-! # Uniform physical grouping and cube clocks

The public cable sweep is charged to the same reserved cable rows as the
interval producer. The declaration and the owned vertex, padding, host and
query loops fit the word-dependent component of (8.3). All coefficients
and the threshold precede the batch, the frame, and the declaration.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube TeamScales Filter VPVNP.BurstRAM

/-- A host-side cable sweep uses at most four times the descriptor charge
because the directed interval pass already spends 23 ticks on each cable. -/
theorem cableSweep_le (l : LabelIndex.Layout) (m : ℕ → ℕ) (z a : ℕ)
    (g : GroupWeights.Layout) (t : TeamNative.Layout) :
    82*l.cableCount ≤ 4*descriptorTicks l m z a g t := by
  have h : 23*l.cableCount ≤ descriptorTicks l m z a g t := by
    unfold descriptorTicks
    change 23*l.cableCount ≤ LabelIndex.directoryTicks l z m+(28+(4*l.labels^2+2)+(2+l.cableCount*23))+_
      +_+_+_+_+_+_
    omega
  omega

/-- The concrete square-label and exterior volume allowance is absorbed by
the local-work scale. The final one covers an empty assignment to a team. -/
theorem cubeUnits_le_localWork {a D n r R : ℕ} {α ξ : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hR : 1 ≤ R) :
    ((Routing.labelCount a α n:ℝ)^2+(exterior ξ r n:ℝ)+1) ≤ 2*localWork a D α ξ r n R := by
  let Z : ℝ := Routing.labelCount a α n
  let X : ℝ := exterior ξ r n
  let L : ℝ := (logWidth r n:ℝ)^D
  have zp : 0 ≤ Z := by dsimp [Z]; positivity
  have xp : 0 ≤ X := by dsimp [X]; positivity
  have rp : 1 ≤ (R:ℝ) := by exact_mod_cast hR
  have p : 1 ≤ Z+R := by linarith
  have ps := (pow_le_pow_left₀ zp (show Z ≤ Z+R by linarith) 2).trans
    (pow_le_pow_right₀ p (by decide : 2 ≤ 10))
  have q : 1 ≤ (Z+R)^10 := one_le_pow₀ p
  have lp : 1 ≤ L := one_le_pow₀ (by exact_mod_cast (GeometryAdviceRate.indexWidths hr hn).1)
  have b : X+(Z+R)^10 ≤ (X+(Z+R)^10)*L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left lp (show 0 ≤ X+(Z+R)^10 by positivity)
  change Z^2+X+1 ≤ 2*((X+(Z+R)^10)*L)
  linarith only [ps,q,b,xp]

/-- Apply the producer's actual epoch multiplicity and degree rectangle to
all grouping and cube stages together. The frame-to-frame time estimate for
`scheduleGroups` and the row/ID/cable estimate share these two allowances. -/
theorem eventually_groupingAndCube {α ξ τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (a bits B C D G K F : ℕ) (small : α*a < 1/10^6) (alphaCap : α ≤ 1/1000)
    (hG : 1 ≤ G) (hK : 1 ≤ K) (growth : τ*Real.logb 2 G ≤ α/10) (fan : τ*Real.logb 2 K ≤ α) :
    ∀ᶠ n : ℕ in atTop, ∀ (r R V z w : ℕ) (l : LabelIndex.Layout) (m : ℕ → ℕ)
      (g : GroupWeights.Layout) (t : TeamNative.Layout) (p : HeaderDecode.Layout),
      1 ≤ r → 1 ≤ R → (V:ℝ) ≤ C*r*(n:ℝ)^(9/10:ℝ) →
      1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(max (G^epochs τ n) (teams α τ K n)+1) →
      l.labels=Routing.labelCount a α n → l.labels=z+1 → g.cells=l.cells → t.groups=g.groups →
      t.r+1 ≤ g.groups → g.groups ≤ l.labels → p.d=g.groups → p.a=a →
      p.cw ≤ w → p.rw ≤ w → w ≤ logWidth r n ^ D →
      ((descriptorTicks l m z a g t+82*l.cableCount:ℕ):ℝ) ≤ 5*publicWork a α r n R ∧
      ((declarationTicks p (a-1) bits + F*(l.labels^2+exterior ξ r n+1):ℕ):ℝ) ≤
        ((512*(a+bits+1)+2*F:ℕ):ℝ)*localWork a D α ξ r n R := by
  filter_upwards [eventually_scheduleTicks (ξ:=ξ) hα a bits B C D small,eventually_ge_atTop 1] with n rate hn
  intro r R V z w l m g t p hr hR hV rows Z hz cells groups team groupCount d axes cw rw width
  have hM := LabelIndex.multiplicity_le hn hτ alphaCap hG hK growth fan
  obtain ⟨desc,decl⟩ := rate r R V _ z w l m g t p hr hR hV hM rows Z hz cells groups team groupCount d axes cw rw width
  have cables := Nat.cast_le (α:=ℝ) |>.mpr (cableSweep_le l m z a g t)
  have cube := mul_le_mul_of_nonneg_left (cubeUnits_le_localWork (a:=a) (D:=D) (α:=α) (ξ:=ξ) hn hr hR) (Nat.cast_nonneg F)
  rw [← Z] at cube
  push_cast at cables decl ⊢
  constructor <;> linarith only [desc,cables,decl,cube]

/-- The fetched grouping fragment on a well-placed physical frame satisfies
(8.3) uniformly, with the exact trace semantics of the signed assembly. -/
theorem eventually_scheduleGroups_trace {α ξ τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (a bits B C D G K : ℕ) (small : α*a < 1/10^6) (alphaCap : α ≤ 1/1000)
    (hG : 1 ≤ G) (hK : 1 ≤ K) (growth : τ*Real.logb 2 G ≤ α/10) (fan : τ*Real.logb 2 K ≤ α) :
    ∀ᶠ n : ℕ in atTop, ∀ (r R V z w : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
      (p : Placements) (s t : Bank w) (m mt : Memory w) (es : List (TeamRAM.Event w)),
      let l := LabelIndex.layout (pub 0).val (readings m)
      let header := p.header.decoder p.broadcast
      1 ≤ r → 1 ≤ R → (V:ℝ) ≤ C*r*(n:ℝ)^(9/10:ℝ) →
      1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(max (G^epochs τ n) (teams α τ K n)+1) →
      l.labels=Routing.labelCount a α n → l.labels=z+1 → p.groups.cells=l.cells → p.teams.groups=p.groups.groups →
      p.teams.r+1 ≤ p.groups.groups → p.groups.groups ≤ l.labels → p.header.d=p.groups.groups → p.header.a=a →
      header.cw ≤ w → header.rw ≤ w → w ≤ logWidth r n ^ D →
      AtEntries pub mac (passes pub mac z (a-1) bits m p) s m →
      Runs pub mac (scheduleGroups (a-1) bits) s m es t mt →
      (traceCost es:ℝ) ≤ publicWork a α r n R+((512*(a+bits+1):ℕ):ℝ)*localWork a D α ξ r n R := by
  filter_upwards [eventually_scheduleTicks (ξ:=ξ) hα a bits B C D small,eventually_ge_atTop 1] with n rate hn
  intro r R V z w pub mac p s t m mt es l header hr hR hV rows Z hz cells groups team groupCount d axes cw rw width ready run
  have hM := LabelIndex.multiplicity_le hn hτ alphaCap hG hK growth fan
  obtain ⟨desc,decl⟩ := rate r R V _ z w l (readings m) p.groups p.teams header hr hR hV hM rows Z hz cells groups
    team groupCount d axes cw rw width
  have actual := Nat.cast_le (α:=ℝ) |>.mpr (scheduleGroups_traceCost pub mac z (a-1) bits p ready run)
  change (traceCost es:ℝ) ≤ ((descriptorTicks l (readings m) z p.header.a p.groups p.teams +
    declarationTicks header (a-1) bits:ℕ):ℝ) at actual
  rw [axes,Nat.cast_add] at actual
  exact actual.trans (add_le_add desc decl)

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
