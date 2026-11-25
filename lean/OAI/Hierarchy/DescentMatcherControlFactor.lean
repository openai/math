import OAI.Hierarchy.DescentMatcherRatePolynomials

namespace OAI
/-! # Physical control names in the publicly scheduled ordinary matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony
open scoped Classical
noncomputable section

namespace DateBill

def controlFactor (k D cap K bound : ℕ) :=
  5*extraFactor k D K+Prepared.namesPerWord k D cap K+
    Census.columns (2^k) cap*(15+4*(max 22 bound+6))

/-- This polynomial covers the local field scans, all chooser tables and the labels,
registers and storage slots of every matcher instruction. -/
theorem controlFactor_polynomial (k D cap K bound : ℕ) :
    controlFactor k D cap K bound≤30000*(1+(2^k+D+2*cap+K+bound))^4 := by
  let n:=1+(2^k+D+2*cap+K+bound)
  have components (radix degree lanes keyCount lookup : ℕ) :
      let total := 1+(radix+degree+lanes+keyCount+lookup)
      radix ≤ total ∧ degree ≤ total ∧ lanes ≤ total ∧ keyCount ≤ total ∧
        max 22 lookup ≤ 22+total ∧ 1+(radix+degree+keyCount) ≤ total := by
    dsimp only
    simp only [max_le_iff]
    repeat' constructor <;> omega
  obtain ⟨r,d,c,keys,query,early⟩ := components (2^k) D (2*cap) K bound
  have extra:extraFactor k D K≤1000*n^3 :=
    (extra_polynomial k D K).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left early _))
  have cols:Census.columns (2^k) cap≤n*(1+(1+n)):=by
    unfold Census.columns
    gcongr
  have slots:fields (2^k) D (2*cap)≤n+(n*n+n*n):=by unfold fields;gcongr
  let m:=n+(n*n+n*n)
  have chip : Prepared.namesPerWord k D cap K ≤
      15*(4+n+2*n) + (26+400*(n+1)^3+(n+n*n)*111) +
      (15*(((1+m)+(n+6))+1+n+1)+15+n*(11+4*(14+m*56))+472+411*(n+1)) := by
    unfold Prepared.namesPerWord
    dsimp only
    gcongr
  have surface : controlFactor k D cap K bound ≤ 5*(1000*n^3)+
      (15*(4+n+2*n)+(26+400*(n+1)^3+(n+n*n)*111)+
      (15*(((1+m)+(n+6))+1+n+1)+15+n*(11+4*(14+m*56))+472+411*(n+1)))+
      (n*(1+(1+n)))*(15+4*(22+n+6)) := by
    unfold controlFactor
    gcongr
  change _≤30000*n^4
  apply surface.trans
  dsimp only [m]
  obtain ⟨j,e⟩:=Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 from Nat.ne_of_gt (Nat.add_pos_left (by decide : 0 < 1) _))
  rw [e,Nat.succ_eq_add_one]
  ring_nf
  omega

end DateBill

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
