import OAI.Computability.BorderVNP.CellPrivateTranslateScale
import OAI.Computability.BorderVNP.CellRecordEmitPhysicalCost
import OAI.Computability.BorderVNP.CellSignedRangeSweepCost
import OAI.Computability.BorderVNP.CellSubtotalPhysicalCost

/-! # Resource bound for the real sparse private packet compiler

The coefficients and binary-width exponent depend on the fixed table alphabet
and public record formats. The expanded-load exponent is at most 63 for every
compiled cell. This theorem bounds the finite program that actually receives
the original typed packet.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPrivate

set_option maxHeartbeats 1200000

open CellSparse
open CellSparse.Packet.Emit

private theorem enlarge {x C W W' L a b d e : ℕ} (h : x ≤ C*W^a*L^b)
    (hW : W ≤ W') (hp : 1 ≤ W') (hL : 1 ≤ L) (ha : a ≤ d) (hb : b ≤ e) :
    x ≤ C*(W'^d*L^e) := by
  rw [← Nat.mul_assoc]
  exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hW a).trans
    (Nat.pow_le_pow_right hp ha))) (Nat.pow_le_pow_right hL hb))

/-- Uniform true-clock bound for original typed data, including all four
data-dependent passes, binary packet decoding, and clean transfers. Large
global identifiers are charged by their bit length. -/
theorem translateClock_physical (A T B j G g H R k : ℕ) :
    ∃ K e : ℕ, 0 < K ∧ 0 < e ∧ ∀ (D : Directory) (p M E U V L : ℕ),
      1 ≤ L → D.StaticBounds A M → Packet.storedMass D ≤ A*(M+1)^2 →
      Packet.RawFields D p U → U.size+1 ≤ B*L^j →
      D.CompactFields p V → V.size+1 ≤ G*L^g →
      (∀ r ∈ D.records, (Packet.record r).length ≤ H) →
      (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      (∀ bs ∈ D.reportedCounts, bs.length ≤ R*L^k) →
      translateClock D p ≤ K*(M+E+1)^63*L^e := by
  obtain ⟨C,hC⟩ := translateClock_of_degree 63 (by decide)
  obtain ⟨Cp,hp⟩ := Packet.compiler_input_sizes A B j
  obtain ⟨Cw,jw,_,_,hw⟩ := getRecordGuards_meter_of_width A B j H
  obtain ⟨Cf,jf,_,_,hf⟩ := factorSweep_meter_width A T B j
  obtain ⟨Cr,jr,_,_,hr⟩ := rangeSweep_meter_width A T B j
  obtain ⟨Ct,jt,_,_,ht⟩ := subtotalGuards_meter_static_width A T B j G g R k
  let J := jw+jf+jr+jt+j+1
  let coeff := Cw+Cf+Cr+Ct+Cp
  refine ⟨(C+1)*(coeff+1)^2,J+J+2,by positivity,by omega,?_⟩
  intro D p M E U V L hL hstatic hstore hraw hu hcompact hv hrecords hfactors hreports
  let W := M+E+1
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hm : M+1 ≤ W := by dsimp [W]; omega
  let T₀ := W^63*L^J
  have w : getRecordGuards.meter D ≤ Cw*T₀ :=
    enlarge (hw D p M E U L hstatic hstore hraw hL hu hrecords) (le_refl _) hW hL (by decide) (by dsimp [J]; omega)
  have f : factorSweep.meter D ≤ Cf*T₀ :=
    enlarge (hf D p M U L hL hstatic hstore hraw hu hfactors) hm hW hL (by decide) (by dsimp [J]; omega)
  have r : rangeSweep.meter D ≤ Cr*T₀ :=
    enlarge (hr D p M U L hL hstatic hstore hraw hu hfactors) hm hW hL (by decide) (by dsimp [J]; omega)
  have t : (subtotalGuardsStmt (ExactQuantumFactoring.BitStackProgram.Procedure.identity Packet.Typed.directory)).meter D ≤ Ct*T₀ :=
    enlarge (ht D p M E U V L hstatic hstore hraw hcompact hL hu hv hfactors hreports) (le_refl _)
      hW hL (le_refl _) (by dsimp [J]; omega)
  have hpass : passMeters D ≤ coeff*W^63*L^J := calc
    _ ≤ Cw*T₀+Cf*T₀+Cr*T₀+Ct*T₀ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add w f) r) t
    _ = (Cw+Cf+Cr+Ct)*T₀ := by simp only [Nat.add_mul]
    _ ≤ coeff*T₀ := Nat.mul_le_mul_right _ (by dsimp [coeff]; omega)
    _ = _ := (Nat.mul_assoc ..).symm
  have hb : (Packet.bits D p).length ≤ coeff*W^2*L^J :=
    (hp D p M E U L hL hstatic hstore hraw hu).1.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_right _ (show Cp ≤ coeff by dsimp [coeff]; omega))
      (Nat.pow_le_pow_right hL (by dsimp [J]; omega)))
  exact (hC D p coeff W L J hW hL hpass hb).trans (by gcongr; omega)

end CellPrivate

end BorderVNP
end Computability
end OAI
