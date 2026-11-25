import OAI.Computability.BorderVNP.PackedSelectedEpochNodeFrames
import OAI.Computability.BorderVNP.PackedCellAddressCircuit

/-! # Size and address width of one selected private-width scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Packing Shortening PublicCapacity TeamScales
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The site and cable arrays, supplied port arguments, and birth histogram slots charged
by one selected width computation. -/
noncomputable def widthScanRows (start t j ports : ℕ) : ℕ :=
  let next := before S start t (j+1)
  1 + CellAddressCircuit.count next.sites next.edges ports next.sites + seedCount S start t j

/-- The fixed sewing template determines the overhead per row of the joined input. -/
noncomputable def widthScanFactor := 4*sewFactor e (bins S)+bins S+2

/-- At a grouped public input with at most one port slot per site, the successor histogram
and stable width scan occupy a constant multiple of the joined rectangle. -/
theorem widthScanRows_volume {start t j ports V : ℕ}
    (seeds : seedCount S start t j ≤ V*bins S)
    (hp : ports ≤ ((before S start t j).parallel S.fanIn).sites) :
    widthScanRows S start t j ports ≤ widthScanFactor S*((before S start t j).parallel S.fanIn).volume V := by
  let sub := (before S start t j).parallel S.fanIn
  let next := before S start t (j+1)
  have sew : next.volume V ≤ sewFactor e (bins S)*sub.volume V := by
    rw [show next = sub.sew e (seedCount S start t j) from before_next S start t j]
    exact sub.sew_volume e _ _ _ seeds
  have hv : V ≤ sub.volume V := by unfold Shape.volume; omega
  have hs := seeds.trans (Nat.mul_le_mul_right (bins S) hv)
  change ports ≤ sub.sites at hp
  have hp' : ports ≤ sub.volume V := hp.trans (by unfold Shape.volume; omega)
  have one : 1 ≤ sub.volume V := by unfold Shape.volume; omega
  change 1+CellAddressCircuit.count next.sites next.edges ports next.sites+seedCount S start t j ≤ widthScanFactor S * sub.volume V
  rw [CellAddressCircuit.count,widthScanFactor,Nat.add_mul,Nat.add_mul,Nat.mul_assoc,mul_comm (bins S) _]
  change next.sites+next.edges+V+1 ≤ _ at sew
  omega

/-- The full scan, including its seed input, is sortable with 64 processor address logs.
This follows from the actual padded site, cable and guess ranges at this stage. -/
theorem widthScanRows_log {r n start t ports den cut : ℕ} {i : Fin S.rounds}
    (range : Ranges S r n start t i den cut) (hl : 1 ≤ logWidth r n)
    (hp : ports ≤ ((before S start t i).parallel S.fanIn).sites) :
    Nat.clog 2 (widthScanRows S start t i ports) ≤ 64*logWidth r n := by
  let L := logWidth r n
  let w := 60*L
  obtain ⟨_,_,_,site,_,seed,site',edge',_⟩ := range.words
  have port : ports ≤ 2^w := hp.trans site
  have h : widthScanRows S start t i ports ≤ 16*2^w := by
    dsimp only [widthScanRows,CellAddressCircuit.count]
    have h1 : 1 ≤ 2^w := Nat.one_le_pow _ _ (by decide)
    change _ ≤ 2^w at site' edge' seed
    omega
  have hpow : 16*2^w = 2^(4+w) := by rw [pow_add]; rfl
  have word := Nat.clog_le_of_le_pow (h.trans_eq hpow)
  exact word.trans (by dsimp only [w,L]; omega)

/-- Word operations linear in this scan and cubic in its address length fit the
paper's row-cost convention with a coefficient fixed across all lengths and processors. -/
theorem widthScanRows_cubic {r n start t j ports V : ℕ} (A : ℕ) (hl : 1 ≤ logWidth r n)
    (hs : seedCount S start t j ≤ V*bins S) (hp : ports ≤ ((before S start t j).parallel S.fanIn).sites) :
    A*(widthScanRows S start t j ports)*(64*logWidth r n+1)^3 ≤
      rowWork (A*widthScanFactor S*65^3) V (logWidth r n) 3 ((before S start t j).parallel S.fanIn) := by
  let L := logWidth r n
  have hw : 64*L+1 ≤ 65*L := by dsimp only [L]; omega
  calc
    _ ≤ A*(widthScanFactor S*((before S start t j).parallel S.fanIn).volume V)*(65*L)^3 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left A (widthScanRows_volume S hs hp)) (Nat.pow_le_pow_left hw _)
    _ = _ := by dsimp only [rowWork,L]; ring

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
