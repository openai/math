import OAI.Hierarchy.TaggedRadixPins
import OAI.Hierarchy.CatalystSubstitutionHost

namespace OAI
/-! # The exact outer host on the exposed data of a radix checker -/

noncomputable section
namespace Hierarchy.Tagged.RadixStage
open Catalyst CatalystSubstitution ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p : ℕ}

variable {H : Type} [Fintype H]

/-- Interpret the retained holes as the actual data pins of each contracted
gate. The outer host has no catalyst before the individual calls are installed. -/
def outputHost (os : List (Occurrence F k)) (e : H ≃ Sockets os)
    (N : BitNetwork F (Fintype.card (Fin p ⊕ H))) : Host F k p (Sockets os) where
  width := fun _=>0
  network := pullPins N (fun i => Sum.inl (i.elim (fun j => .inl (.inl j)) (fun h => .inr (e h))))

theorem exactValue_output (os : List (Occurrence F k)) (e : H ≃ Sockets os)
    (N : BitNetwork F (Fintype.card (Fin p ⊕ H))) (v : (Fin p→Bool)→F)
    (ev : ∀ x, (∑ z,TypedWiring.value N (Sum.elim x z)*exactWeight os (z ∘ e.symm)) = v x)
    (x : Port p (fun _ : Fin k=>0)→Bool) :
    exactValue os (outputHost os e N) x = ideal (fun _ : Fin k=>0) v x := by
  let pins := x ∘ Sum.inl
  have eq (z : Sockets os→Bool) : (outputHost os e N).coeff x z =
      TypedWiring.value N (Sum.elim pins (z∘e)) := by
    unfold Host.coeff outputHost
    rw [pullPins_value]
    apply congrArg (TypedWiring.value N)
    funext i
    cases i <;> rfl
  have full : ∀ j : Wire (fun _ : Fin k => 0), x (.inr (j,false))=x (.inr (j,true)) := by
    intro j; exact Fin.elim0 j.2
  rw [ideal,ite_eq_left full]
  unfold exactValue
  simp_rw [eq]
  rw [← (Equiv.arrowCongr e (Equiv.refl Bool)).sum_comp]
  simpa [Equiv.arrowCongr,Function.comp_def,pins] using ev pins

theorem output_exact_gap (os : List (Occurrence F k)) (e : H ≃ Sockets os)
    (N : BitNetwork F (Fintype.card (Fin p ⊕ H))) (v : (Fin p→Bool)→F)
    (ev : ∀ x, (∑ z,TypedWiring.value N (Sum.elim x z)*exactWeight os (z ∘ e.symm)) = v x)
    (G : ℝ) : (tableApprox (outputHost os e N).width (exactValue os (outputHost os e N))).Gap v G := by
  intro P
  left
  funext x
  change Port p (fun _ : Fin k => 0) → Bool at x
  change (tableApprox (outputHost os e N).width (exactValue os (outputHost os e N))).coeff x -
    ideal (fun _ : Fin k => 0) v x = 0
  apply sub_eq_zero.mpr
  exact (tableApprox_coeff (outputHost os e N).width (exactValue os (outputHost os e N)) x).trans
    (exactValue_output os e N v ev x)

end Hierarchy.Tagged.RadixStage

end
end OAI
