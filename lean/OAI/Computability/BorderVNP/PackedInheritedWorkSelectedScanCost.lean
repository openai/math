import OAI.Computability.BorderVNP.PackedInheritedWorkPrepCost
import OAI.Computability.BorderVNP.PackedNamedPortHeaders
import OAI.Computability.BorderVNP.PackedFrozenHistoryCapacity

/-! # Sparse gate cost of a grouped exterior directory on the selected word width -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity Packing Packing.Inherited
open Packing.Inherited.WorkWords EnrichedOuter TeamScales
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m np : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
variable {start : ℕ}

/-- Each copy of each grouped original port has a slot in the site's actual old
rectangle. The same inequality holds on all intermediate source levels. -/
theorem widthPorts_le (base : np ≤ CoverScale.sites (Cube D) start) (t j : ℕ) :
    Parallel.nestedCapacity S.fanIn (portCapacity S np t) j ≤ (before S start t j).sites := by
  rw [path_count]
  exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ base)).trans ((FrozenTape.ports_fit S start).2 t j)

/-- A bounded site, cable and grouped port rectangle pays for the work and extent scans. -/
theorem widthCharge_cubic {s n w L : ℕ} (edge : ℕ) (ports : n ≤ s) (sites : s ≤ 2^w)
    (edges : edge ≤ 2^w) (word : w = 60*L) (hL : 1 ≤ L) :
    Prep.charge s edge n w ≤ 32000*(s+edge+1)*66^3*L^3 := by
  let R := 8*(s+edge+1)
  have rs : 1+CellAddressCircuit.count s edge n s ≤ R := by dsimp [CellAddressCircuit.count,R]; omega
  have log : Nat.clog 2 R ≤ w+5 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    have pos : 0<2^w := by positivity
    dsimp only [R]
    norm_num
    omega
  have size := Prep.charge_cubic rs (show w ≤ w+5 by omega) log
  have bits : w+5+1 ≤ 66*L := by omega
  apply size.trans ((Nat.mul_le_mul_left (4000*R) (Nat.pow_le_pow_left bits 3)).trans_eq ?_)
  dsimp only [R]
  ring

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
