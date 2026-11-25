import OAI.ThreeFlat.Diagonal.PhysicalProgramEffects
import OAI.ThreeFlat.Diagonal.PhysicalMoveShrinkEnergy
import OAI.ThreeFlat.Diagonal.PhysicalMoveRefreshEnergy

namespace OAI
/-! # All chronological physical histories satisfy the program's energy bounds -/

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

def State.Within {d l : ℕ} (A : State d l) (v : Totals) : Prop :=
  A.energy ≤ v.energy ∧ (A.positions:ℝ) ≤ v.sites

private theorem within_cast {d l l' : ℕ} (e : l = l') (A : State d l) (v : Totals) :
    (e ▸ A : State d l').Within v ↔ A.Within v := by cases e; rfl

/-- A bound for every state, including each intermediate state before its update. -/
def Run.Budgeted : {d l : ℕ} → {A : State d l} → Run F A → List Effect → Totals → Prop
  | _, _, _, .done A, [], v => A.Within v
  | _, _, A, .step _ next, u :: us, v => A.Within v ∧ ∀ i, (next i).Budgeted us (u.apply v)
  | _, _, _, _, _, _ => False

private theorem budget_recast {d l l' : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) (us : List Effect) (v : Totals) :
    (Program.recast e A r).Budgeted us v ↔ r.Budgeted us v := by cases e; rfl

theorem State.energy_nonneg {d l : ℕ} (A : State d l) : 0 ≤ A.energy := by
  unfold State.energy
  positivity

private theorem energy_allowance {a b c e E p P : ℝ} (he : e ≤ E)
    (hp : p ≤ P) (hp0 : 0 ≤ p) (he0 : 0 ≤ e) (hc : 0 ≤ c) (hb : b ≤ c) :
    a*e+b*p^2 ≤ max 0 a*E+c*P^2 := by
  have h1 := mul_le_mul (le_max_right 0 a) he he0 (le_max_left 0 a)
  have h2 := mul_le_mul hb (pow_le_pow_left₀ hp0 hp 2) (sq_nonneg p) hc
  exact add_le_add h1 h2

set_option maxHeartbeats 1200000 in
theorem Program.run_budgeted {s : ℕ} (P : Program F s) (rem : ℕ)
    (A : State (2^s) (P.charge+rem)) (v : Totals) (hv : A.Within v) :
    (P.run rem A).Budgeted (P.effects shrinkError) v := by
  induction P generalizing v with
  | done s => exact hv
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    let u : Effect := ⟨126/127,max 0 (shrinkError T s (2^t)),true⟩
    change (recast e A (.step R _)).Budgeted (u :: tail.effects shrinkError) v
    apply (budget_recast ..).2
    have hB : B.Within v := (within_cast e A v).2 hv
    refine ⟨hB,fun i => ih (R.next i) (u.apply v) ⟨?_,?_⟩⟩
    · have h := shrinkBinary_energy T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B i
      have h' := energy_allowance (a:=(126/127:ℝ)) (b:=shrinkError T s (2^t)) hB.1 hB.2
        (by positivity) B.energy_nonneg (le_max_left 0 _) (le_max_right 0 _)
      change (R.next i).energy ≤ 126/127*v.energy+max 0 (shrinkError T s (2^t))*v.sites^2
      exact h.trans (by simpa only [max_eq_right (by norm_num : (0:ℝ) ≤ 126/127)] using h')
    · have hp := shrinkBinary_positions T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B i
      have hh : 4*((R.next i).positions:ℝ) ≤ B.positions := by exact_mod_cast hp
      change ((R.next i).positions:ℝ) ≤ v.sites/4
      linarith [hB.2]
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T B hm hh sym rows zero conn
    let u : Effect := ⟨max 0 ((1+h+pad:ℕ)+2*C:ℝ),T.error,false⟩
    change (recast e A (.step (recastMove degree R) _)).Budgeted (u :: tail.effects shrinkError) v
    apply (budget_recast ..).2
    have hB : B.Within v := (within_cast e A v).2 hv
    refine ⟨hB,fun i => ih _ (u.apply v) ?_⟩
    apply Move.map_bound_degree degree R (fun E p => E ≤ (u.apply v).energy ∧ (p:ℝ) ≤ (u.apply v).sites) _ i
    intro j
    constructor
    · apply (refreshBinary_energy T B hm hh sym rows zero conn j).trans
      exact energy_allowance hB.1 hB.2 (by positivity) B.energy_nonneg T.nonneg le_rfl
    · change ((R.next j).positions:ℝ) ≤ v.sites
      simpa only [R,refreshBinary_positions] using hB.2

/-- The final bound uses exactly the chronological list of stage effects. -/
theorem Run.allLeaves_of_budgeted {d l : ℕ} {A : State d l} (r : Run F A) (us : List Effect)
    (v : Totals) (h : r.Budgeted us v) :
    r.AllLeaves (fun E n => E ≤ (us.foldl Effect.apply v).energy ∧
      (n:ℝ) ≤ (us.foldl Effect.apply v).sites) := by
  induction r generalizing us v with
  | done A => cases us with
    | nil => exact h
    | cons a as => exact False.elim h
  | step R next ih => cases us with
    | nil => exact False.elim h
    | cons a as => exact fun i => ih i as (a.apply v) (h.2 i)

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
