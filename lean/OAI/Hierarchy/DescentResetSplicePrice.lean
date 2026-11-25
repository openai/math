import OAI.Hierarchy.DescentResetCoefficient
import OAI.Hierarchy.DescentCompilerIteration

namespace OAI
/-! # Paying both endpoint-table cables before choosing the shrink count -/

namespace Hierarchy.DescentResetInvoice

def splicedRate (h C : ℕ) : ℝ := internalRate h C + 2

def splicedExteriorRate (h C : ℕ) (β : ℝ) (tetherHops : ℕ) : ℝ :=
  exteriorRate h C β tetherHops + 2

/-- Opening the old endpoints introduces one connecting cable at each end of
each original wire. This bills both copies of its original width. -/
theorem splice_invoice {X E ε bank opened β : ℝ} (h C tetherHops : ℕ)
    (allowance : 0≤ε)
    (initial : bank ≤ internalRate h C*(X+ε) + exteriorRate h C β tetherHops*E)
    (splice : opened ≤ bank + 2*(X+E)) :
    opened ≤ splicedRate h C*(X+ε) + splicedExteriorRate h C β tetherHops*E := by
  unfold splicedRate splicedExteriorRate
  linarith only [initial,splice,allowance]

/-- Fix the number of subrounds with the coefficient for the complete spliced
network. The later degree reservation can be any function of that count. -/
theorem choose_spliced_phases {ρ : ℝ} (h C : ℕ) (positive : 0≤ρ) (strict : ρ<1)
    (reservation : ℕ→ℕ) :
    ∃ t : ℕ, 0<t ∧ splicedRate h C*ρ^t≤1/2 ∧
      ∃ n₀ : ℕ, ∀ n≥n₀,4*reservation t≤2^n :=
  DescentCompiler.choose_phases positive strict reservation

/-- The side-specific old terminal adds one trunk carrying the entire true-side word. -/
def reentryRate (h C : ℕ) : ℝ := splicedRate h C+1

def reentryExteriorRate (h C : ℕ) (β : ℝ) (Ht : ℕ) : ℝ := splicedExteriorRate h C β Ht+1

theorem choose_reentry_phases {ρ : ℝ} (h C : ℕ) (positive : 0≤ρ) (strict : ρ<1)
    (reservation : ℕ→ℕ) :
    ∃ t : ℕ,0<t ∧ reentryRate h C*ρ^t≤1/2 ∧
      ∃ n₀ : ℕ,∀ n≥n₀,4*reservation t≤2^n :=
  DescentCompiler.choose_phases positive strict reservation

end Hierarchy.DescentResetInvoice

end OAI
