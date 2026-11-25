import OAI.Hierarchy.TaggedRadixOutput
import OAI.Hierarchy.TaggedRadixSockets
import OAI.Hierarchy.TaggedRadixSeal
import OAI.Hierarchy.CatalystSubstitutionFamily

namespace OAI
/-! # Appended banks of exact gates and the physical installation interface -/

noncomputable section
namespace Hierarchy.Tagged.RadixStage
open Catalyst CatalystSubstitution ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p : ℕ}

variable {H : Type} [Fintype H]

/-- Sealing a physical radix checker puts precisely the original data and
the installed catalyst ports on the boundary. All addressed sort sockets
are paid for exactly once by the replacement size. -/
theorem install_output (os : List (Occurrence F k)) (e : H ≃ Sockets os)
    (N : BitNetwork F (Fintype.card (Fin p ⊕ H))) (v : (Fin p→Bool)→F)
    (ev : ∀ x, (∑ z,TypedWiring.value N (Sum.elim x z)*exactWeight os (z ∘ e.symm)) = v x)
    (G : ℝ) (good : ∀ o ∈ os,o.replacement.Gap o.target G) :
    ∃ X : Approximation F k p, X.size=N.cells+N.internal+p+(os.map (·.replacement.size)).sum ∧
      X.Gap v (G-2*(k:ℝ)*(os.length:ℝ)) := by
  let C := outputHost os e N
  refine ⟨install os C,?_,install_gap os C v G (output_exact_gap os e N v ev G) good⟩
  have size := install_size os C
  have : IsEmpty (Wire (fun _ : Fin k => 0)) :=
    ⟨fun t => Fin.elim0 t.2⟩
  have bill : hostSize C = N.cells+N.internal+p+Fintype.card (Sockets os) := by
    simp [C,hostSize,outputHost,pullPins,Port,Fintype.card_sum]
   ; omega
  rw [bill,sockets_card] at size
  omega

end Hierarchy.Tagged.RadixStage

end
end OAI
