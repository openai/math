import Mathlib.Tactic

namespace OAI
/-! # Charging a reset to internal wires, packing allowance and exterior wires -/

namespace Hierarchy.DescentResetInvoice

/-- This coefficient is fixed with the rotor degree and per-bit supply multiplicity,
before choosing the degree of a reset stage or its dyadic grouping factor. -/
def internalRate (h C : ℕ) : ℝ := 1700*(1+((2*h+4)*(2*h*C+2):ℕ))

def exteriorRate (h C : ℕ) (β : ℝ) (tetherHops : ℕ) : ℝ :=
  internalRate h C * (β+1) + tetherHops + 1

/-- Up to two oriented copies of the good-base allocation can be present.
The three components are measured in the same original units. The direct
links can be counted again at their full original width, covering a join that
is implemented as a separate old contact instead of a rotor pin. -/
theorem component_invoice {X E ε β M span rotor trees joins : ℝ} (h C tetherHops : ℕ)
    (hX : 0≤X) (hE : 0≤E) (hε : 0≤ε) (hβ : 0≤β)
    (hub : M≤2*X+(β+1)*E+ε) (bases : span≤4*(M+ε))
    (good : rotor≤42*((2*h+4)*(2*h*C+2):ℕ)*span)
    (fallback : trees≤M+ε+tetherHops*E) (direct : joins≤X+E) :
    rotor+trees+joins ≤ internalRate h C*(X+ε)+exteriorRate h C β tetherHops*E := by
  let κ : ℝ := ((2*h+4)*(2*h*C+2):ℕ)
  have hk : 0≤κ := Nat.cast_nonneg _
  have bill : rotor ≤ 168*κ*(M+ε) := by
    calc
      rotor ≤ 42*κ*span := good
      _ ≤ 42*κ*(4*(M+ε)) := mul_le_mul_of_nonneg_left bases (by positivity)
      _ = _ := by ring
  have fold : rotor+trees+joins ≤ (168*κ+1)*(M+ε) + tetherHops*E + (X+E) := by
    linarith only [bill,fallback,direct]
  have hub' : M+ε ≤ 2*(X+ε)+(β+1)*E := by linarith only [hub]
  have paid := mul_le_mul_of_nonneg_left hub' (by positivity : 0≤168*κ+1)
  have slack : (168*κ+1)*2+1 ≤ internalRate h C := by
    change (168*κ+1)*2+1 ≤ 1700*(1+κ)
    linarith
  have xs := mul_le_mul_of_nonneg_right slack (add_nonneg hX hε)
  have rail : 168*κ+1 ≤ internalRate h C := by
    change 168*κ+1≤1700*(1+κ)
    linarith
  have es := mul_le_mul_of_nonneg_right rail (mul_nonneg (by linarith : 0≤β+1) hE)
  unfold exteriorRate
  linarith only [fold,paid,xs,es,hε]

/-- The original bundle amount and the integer number of rotor bits can differ.
The configured raw-base receipt translates back to its actual reserved amount. -/
theorem raw_base_payment {bits : ℕ} {unit F B : ℝ} (positive : 0<unit) (hb : 0<bits) :
    (unit/bits)*(F*(B/unit*bits))=F*B := by
  have b : (bits:ℝ)≠0 := by exact_mod_cast hb.ne'
  field_simp [positive.ne',b]

end Hierarchy.DescentResetInvoice

end OAI
