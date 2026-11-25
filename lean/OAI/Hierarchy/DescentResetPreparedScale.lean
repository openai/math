import OAI.Hierarchy.DescentScalarGrowth
import OAI.Hierarchy.DescentResetPreparedInvoice
import OAI.Hierarchy.DescentResetRootControlScale
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! A polynomial in the genuine public scalar root control pays every instruction per
host and packed group. Its degree and leading constant are independent of the cut. -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentScalarGrowth DescentGLNielsen DescentSixParty.Chronology DescentCompiler.TerminalScale Filter
noncomputable section

def rootCoefficient (D n Ht u : ℕ) : Charges where
  cap:=u
  limbs:=u
  depth:=3*u*u
  projections:=2*u+(2*u)*u
  pages:=2*((2*u)*(2+2^n)+(2*u)*(2^n+1))
  arity:=u
  matrix:=u
  scalar:=(u+1)+u+(2^n+1)+2*(((u+1)*u)*(2^n+1))*2^Ht
  dimension:=u
  guardWork:=10000*(D+1)^2*(2^Ht+1)
  rowWork:=1+u*((500+23*u)+11)

theorem issued_coefficient (D cap n k high low Ht dim read u : ℕ)
    (arity : arityLimit D (2^k) cap n k ≤ u) (geometry : high+low ≤ u)
    (dimension : dim ≤ u) (operands : read ≤ 500+23*u) :
    (issuedCharges D cap (2^k) n k high low Ht dim read).total 1 1 1 ≤
      (rootCoefficient D n Ht u).total 1 1 1 := by
  have slots:inputCount D (2^k) cap n k ≤ u:=(le_max_right ..).trans arity
  have parts (a b c d : ℕ) : a≤a+b+(c+d) ∧ c≤a+b+(c+d) ∧ d≤a+b+(c+d) :=by omega
  obtain ⟨left, middle, right⟩ := parts (2^k) (D*2^k) (2^k*(2*cap)) (DescentSharedBookScan.width k (2^n) D)
  have nodes : 2^k≤u:=left.trans slots
  have rank : DescentSharedBookScan.width k (2^n) D≤u:=right.trans slots
  have ports : cap≤u:=(Nat.le_mul_of_pos_left cap (by decide : 0<2)).trans
    ((Nat.le_mul_of_pos_left (2*cap) (Nat.two_pow_pos k)).trans (middle.trans slots))
  have depth:k ≤ u:= (Nat.lt_two_pow_self (n:=k)).le.trans nodes
  have length:= (length_le (high+low)).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 3 geometry) geometry)
  have codes: (DescentHostDirectory.codes k).card ≤ 2*u:=by
    have upper:=DescentHostDirectory.codes_card k
    rw [pow_succ] at upper
    omega
  have pages:=RootTemplates.page_count k (2^n)
  unfold Charges.total Charges.retile Charges.projected Charges.signed Charges.rom Charges.catalog
  dsimp only [issuedCharges,rootCoefficient]
  rw [pages]
  unfold count DescentFallbackShapeTable.imageSize DescentFallbackShapeTable.rows
  gcongr

attribute [local fun_prop] DescentScalarGrowth.Polynomial poly_const poly_var poly_add poly_mul

theorem coefficient_polynomial (D n Ht : ℕ) :
    ∃C d : ℕ,∀u,(rootCoefficient D n Ht u).total 1 1 1 ≤ C*(u+1)^d := by
  change Polynomial (fun u=>(rootCoefficient D n Ht u).total 1 1 1)
  unfold Charges.total Charges.retile Charges.signed Charges.projected Charges.rom Charges.catalog
  dsimp only [rootCoefficient]
  fun_prop

theorem coefficient_scale (D n Ht rate : ℕ) :
    ∃C rate' : ℕ,∀J u,u ≤ scale J rate →
      (rootCoefficient D n Ht u).total 1 1 1 ≤ C*scale J rate' := by
  obtain ⟨C,d,poly⟩:=coefficient_polynomial D n Ht
  refine ⟨C*2^d,rate*d,fun J u bound=>?_⟩
  have pos:0 < scale J rate:=Nat.two_pow_pos _
  have grow:=Nat.pow_le_pow_left (show u+1 ≤ 2*scale J rate by omega) d
  have lift:scale J rate^d=scale J (rate*d) :=by
    unfold scale
    rw [←pow_mul]
    congr 1
    ring
  rw [mul_pow,lift] at grow
  exact (poly u).trans ((Nat.mul_le_mul_left C grow).trans_eq (Nat.mul_assoc ..).symm)

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
