import OAI.ThreeFlat.Diagonal.PhysicalStageBinary
import OAI.ThreeFlat.Diagonal.PhysicalRefreshCopies
import OAI.ThreeFlat.Diagonal.PhysicalIncidentWidth

namespace OAI
/-! # Local native work on the successors of the binary refresh move -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Expander Computability.VPVNP.Compression CompressorPacking
open scoped BigOperators Classical
noncomputable section

private theorem total_charge {r p w p' w' : ℕ} (m : ℕ) (hr : r ≤ p+2*w) :
    p'+2*w'+m*r ≤ (2*m+2)*(p+w+p'+w') := by
  calc
    _ ≤ p'+2*w'+m*(p+2*w) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
    _ = m*p+(2*m)*w+1*p'+2*w' := by ring
    _ ≤ (2*m+2)*p+(2*m+2)*w+(2*m+2)*p'+(2*m+2)*w' := by gcongr <;> omega
    _ = _ := by ring

private theorem peak_charge {r b w w' : ℕ} (m D : ℕ)
    (hr : r ≤ (1+2*m*m)*(1+w)) (hb : b ≤ 2*D*w') :
    1+b+r ≤ (2+2*m*m+2*D)*(1+w+w') := by
  calc
    _ ≤ (1+w)+2*D*w'+(1+2*m*m)*(1+w) :=
      Nat.add_le_add (Nat.add_le_add (by omega) hb) hr
    _ = (2+2*m*m)*(1+w)+(2*D)*w' := by ring
    _ ≤ (2+2*m*m+2*D)*(1+w)+(2+2*m*m+2*D)*w' :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
        (Nat.mul_le_mul_right _ (Nat.le_add_left ..))
    _ = _ := by ring

variable {s rem h pad : ℕ} {F : Type} [Field F] {H γ : ℝ} {c : Fin (2^s) → Fin (2^s) → ℕ}
    (T : RefreshMotif.Table F c (1+h+pad) H) (A : State (2^s) (s+rem))
    (hm : 2 ≤ 2^s) (hh : 0 < h) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
    (zero : ∀ i, c i i=0) (conn : Bound (transition c h) ℝ γ)

/-- Each new port has one kernel field, its incident half-widths, and the copy count
of its actual base and residual lane. -/
def refreshBinaryCharge (i : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (v : ((refreshBinary T A hm hh sym rows zero conn).next i).Site) : ℕ :=
  1+((refreshBinary T A hm hh sym rows zero conn).next i).incidentWidth v+
    refreshCopies T A (splitWord s rem) (Native.tagOrdinal s).symm
      (show (A.Base × BitWord rem) × Fin (2^s) from v).1

set_option maxRecDepth 8192 in
theorem refreshBinaryCharge_sum (i : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count) :
    let X := (refreshBinary T A hm hh sym rows zero conn).next i
    (∑ v, refreshBinaryCharge T A hm hh sym rows zero conn i v) ≤
       (2*2^s+2)*(A.positions+A.widthSum+X.positions+X.widthSum) := by
  let X := (refreshBinary T A hm hh sym rows zero conn).next i
  let r := refreshCopies T A (splitWord s rem) (Native.tagOrdinal s).symm
  let localR (v : X.Site) := r (show (A.Base × BitWord rem) × Fin (2^s) from v).1
  have repeatSum : (∑ v : X.Site, localR v) = 2^s*∑ v, r v := by
    change (∑ v : (A.Base × BitWord rem) × Fin (2^s), r v.1) = _
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_id, Finset.mul_sum]
  change (∑ v : X.Site, (1+X.incidentWidth v+localR v)) ≤ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,Nat.cast_id,
    Nat.mul_one, X.sum_incidentWidth, repeatSum]
  exact total_charge (2^s) (refreshCopies_sum_le T A (splitWord s rem) (Native.tagOrdinal s).symm)

set_option maxRecDepth 8192 in
theorem refreshBinaryCharge_le (i : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (v : ((refreshBinary T A hm hh sym rows zero conn).next i).Site) :
    let X := (refreshBinary T A hm hh sym rows zero conn).next i
    refreshBinaryCharge T A hm hh sym rows zero conn i v ≤
      (2+2*(2^s)*(2^s)+2*(1+h+pad))*(1+A.maxWidth+X.maxWidth) := by
  let X := (refreshBinary T A hm hh sym rows zero conn).next i
  exact peak_charge (2^s) (1+h+pad)
    (refreshCopies_le T A (splitWord s rem) (Native.tagOrdinal s).symm
      (show (A.Base × BitWord rem) × Fin (2^s) from v).1)
    (X.incidentWidth_le v)

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
