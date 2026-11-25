import OAI.Hierarchy.PhysicalTracePlan
import OAI.ThreeFlat.Diagonal.PhysicalTreeSize

namespace OAI
/-! # The number of true terminal sites after recasting the cursor run -/

namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage
open scoped Classical

variable {F : Type} [Field F]

private theorem recast_sites {d l l' bound : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l'))
    (h : ∀ z, Fintype.card (r.plan.finish z).Site ≤ bound) :
    ∀ z, Fintype.card ((Program.recast e A r).plan.finish z).Site ≤ bound := by
  cases e
  exact h

private theorem positions_cast {d l l' : ℕ} (e : l=l') (X : State d l) :
    (e ▸ X : State d l').positions = X.positions := by cases e; rfl

private theorem children_positive {s : ℕ} (P : Program F s) : 0 < P.childrenProduct := by
  induction P <;> simp only [Program.childrenProduct] <;> positivity

private theorem finish_sites_le {s : ℕ} (P : Program F s) (rem : ℕ)
    (X : State (2^s) (P.charge + rem)) (h : (P.run rem X).plan.History) :
    Fintype.card ((P.run rem X).plan.finish h).Site ≤ X.positions := by
  apply Fintype.card_le_of_surjective ((P.run rem X).plan.destination h)
  intro v
  have positive : 0 < Nat.card {x // (P.run rem X).plan.destination h x = v} := by
    rw [P.run_destinationSize rem X h v]
    exact children_positive P
  obtain ⟨⟨x,hx⟩⟩ := (Nat.card_pos_iff.mp positive).1
  exact ⟨x,hx⟩

/-- The public size bound counts actual finish sites for every history of the recast run. -/
theorem run_sites (B : Block F) {axes : ℕ} (hk : 2≤axes+1)
    (low offsets slots passes : ℕ) (fit : B.blockCharge*passes≤axes+1)
    (h : (Physical.run B hk low offsets slots passes fit).plan.History) :
    Fintype.card ((Physical.run B hk low offsets slots passes fit).plan.finish h).Site ≤
      (axes+1)*2^(axes+1) := by
  let P := B.repeat passes
  let rem := axes+1-P.charge
  let A := B.cursorState hk low offsets slots
  have split : axes+1=P.charge+rem := by
    dsimp [P,rem]
    rw [B.charge_repeat]
    omega
  let A' : State (2^B.exponent 0) (P.charge+rem) := split ▸ A
  apply recast_sites split A (P.run rem A') _ h
  intro z
  exact (finish_sites_le P rem A' z).trans_eq
    ((positions_cast split A).trans (B.cursorState_positions hk low offsets slots))

end Hierarchy.TraceDistribution.Physical

end OAI
