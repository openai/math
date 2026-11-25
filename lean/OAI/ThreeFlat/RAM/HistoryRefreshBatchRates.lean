import OAI.ThreeFlat.RAM.HistoryRefreshBatch

namespace OAI
/-! # Scalar refresh batch cost bounds -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

private theorem batch_units_le (r d w exponent lut g f p comp : ℕ)
    (level : exponent=Diagonal.HistogramTileNetwork.siteHeight r d) (width : exponent≤w)
    (scan : comp≤2^exponent*(32000*(exponent+1)^3)) :
    let n := r*(2^lut*(lut+1))+g*comp
    (1+exponent+(r+g)+(8*n+r*lut+g*(3*(r*f))))+(r*p+4*n) ≤
      batchUnits lut g f d p*((w+1)^3*(1+r)) := by
  intro n
  let U := (w+1)^3*(1+r)
  have hpow : 0<(w+1)^3 := by positivity
  have rU : r≤U := by
    have h := Nat.le_mul_of_pos_left (1+r) hpow
    dsimp only [U];omega
  have oneU : 1≤U := Nat.mul_pos hpow (by omega : 0<1+r)
  have ew : 1+exponent≤U := by
    have base : (w+1)^1≤(w+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
    have scale := Nat.le_mul_of_pos_right ((w+1)^3) (by omega : 0<1+r)
    simp only [pow_one] at base
    dsimp only [U];omega
  have cU : comp≤(64000*(d+1))*U := by
    have round := Diagonal.HistogramTileNetwork.siteHeight_capacity r d
    rw [←level] at round
    calc
      _ ≤ 2^exponent*(32000*(exponent+1)^3) := scan
      _ ≤ ((r+1)*(2*(d+1)))*(32000*((w+1)^3)) :=
        Nat.mul_le_mul round (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ width) 3))
      _ = _ := by dsimp [U];ring
  have nU : n≤(2^lut*(lut+1)+g*(64000*(d+1)))*U := by
    calc
      _ ≤ U*(2^lut*(lut+1))+g*((64000*(d+1))*U) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ rU) (Nat.mul_le_mul_left g cU)
      _ = _ := by ring
  have groups := Nat.mul_le_mul_left g oneU
  rw [Nat.mul_one] at groups
  have all := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add ew rU) groups) (Nat.mul_le_mul_left 12 nU))
    (Nat.mul_le_mul_right lut rU)) (Nat.mul_le_mul_right (g*(3*f)) rU))
    (Nat.mul_le_mul_right p rU)
  calc
    _ = (1+exponent)+r+g+12*n+r*lut+r*(g*(3*f))+r*p := by ring
    _ ≤ _ := all
    _ = _ := by unfold batchUnits;dsimp [U];ring

private theorem batch_charge {sc overhead units U load pins rows ticks : ℕ}
    (job : ticks≤ sc*load) (budget : load+(pins+4*rows)≤units*U) :
    ticks+overhead*(pins+4*rows)≤(sc+overhead)*units*U := by
  have h1 := Nat.mul_le_mul_left sc (show load≤units*U by omega)
  have h2 := Nat.mul_le_mul_left overhead (show pins+4*rows≤units*U by omega)
  calc
    _ ≤ sc*(units*U)+overhead*(units*U) := Nat.add_le_add (job.trans h1) h2
    _ = _ := by ring


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
