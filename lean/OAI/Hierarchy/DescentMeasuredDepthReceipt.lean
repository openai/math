import OAI.Hierarchy.DescentMeasuredDepthSource

namespace OAI
/-! # The freshly written reset depths and all old data in the same memory -/
noncomputable section
namespace Hierarchy.DescentMeasuredPriming.Depth
open DescentBaseProfile ProtocolRAM DescentColonies DescentMeasuredHeader DescentPackedExchange
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {w H k Δ : ℕ}
local notation "M" => (H*(k+1)+H*Δ)*2^k
variable (lo f r B K scratch : ℕ)
local notation "L" => layout lo H k Δ f r B scratch
local notation "hd" => header lo H k Δ
local notation "dt" => payload lo H k Δ
local notation "now" => memory (H:=H) (k:=k) (Δ:=Δ) lo f r B scratch

theorem bank_frame (m : Memory w) (ahead : start lo H k Δ≤ scratch) {j i : ℕ}
    (lane : j<11) (data : j≠4) (cell : i<span M) : now m ((bank lo M j).base+i)=m ((bank lo M j).base+i) := by
  have sr : H≤ span M := by
    apply le_trans _ (Nat.le_pow_clog (by decide) M)
    apply le_trans _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    have h:=Nat.mul_le_mul_left H (show 1≤k+1 by omega);omega
  change lo+11*span M≤ scratch at ahead
  have low:=Nat.mul_le_mul_right (span M) lane
  simp only [Nat.succ_mul] at low
  apply frame
  · change lo+j*span M+i<scratch;omega
  · change lo+j*span M+i<lo+4*span M ∨ lo+4*span M+H≤lo+j*span M+i
    by_cases before : j<4
    · left
      have h:=Nat.mul_le_mul_right (span M) before
      simp only [Nat.succ_mul] at h;omega
    · right
      have h:=Nat.mul_le_mul_right (span M) (show 5≤j by omega);omega

theorem receipt (m : Memory w) (ns : Native.Neighbors H) (rows : Native.Rows H (2^k))
    (next : Port H Δ→Option (Fin H)) (traffic : Port H Δ→Fin (2^k)→ℕ)
    (addressed : ∀p : Port H Δ,next p=(ns[p.1.val])[p.2.val]?)
    (ahead : start lo H k Δ≤ scratch) (room : (L).base (k-f+2)<2^w) (numeric : decayExponent Δ<2^w ∧ k<2^w)
    (headerRoom : finish lo H k Δ<2^w) (old : Resident lo H k Δ f B K m)
    (peers : ∀p : Port H Δ,m ((hd).neighbor.base+(slot H Δ p).val)=(target (next p):Word w))
    (loads : oldLoads dt (measuredLoad rows) traffic m) (totals : ∀v,Native.totalWeight rows v<2^w)
    (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) :
    (text lo H k Δ f r B scratch w).Exec m (now m) ((L).clocks w (k-f)+(6+5*H)) ∧
    contents (k:=k) hd (measuredDepth ns rows Δ r f B) next f B K (now m) ∧
    dataStatic (H:=H) (k:=k) (Δ:=Δ) dt (now m) ∧ oldLoads dt (measuredLoad rows) traffic (now m) := by
  have possible := headerFits lo H k Δ headerRoom
  have data := dataFits lo H k Δ headerRoom
  have source : (L).Source ns rows m := by
    refine ⟨fun v i=>?_,fun v i=>?_⟩
    · change m ((dt).sites.base + v.val*2^k + i.val) = _
      rw [Nat.add_assoc]
      exact (loads.1 v i).trans (by rfl)
    · have h:=peers (v,i)
      rw [addressed] at h
      change m ((hd).neighbor.base + v.val*Δ + i.val) = _
      rw [Nat.add_assoc, Nat.mul_comm v.val, Nat.add_comm (Δ*v.val) i.val]
      exact h.trans (by rfl)
  obtain ⟨steps,read⟩:=depth_exec lo f r B scratch m ns rows ahead room numeric source totals degree
  have residentNow:=resident lo f r B K scratch m old ahead
  refine ⟨steps,resident_contents _ _ _ _ _ _ _ _ residentNow _ _ read ?_,
    resident_static _ _ _ _ _ _ _ _ residentNow,?_,?_⟩
  · intro p
    exact (bank_frame lo f r B scratch m ahead (j:=5) (by decide) (by decide)
      ((slot H Δ p).isLt.trans_le possible.ports)).trans (peers p)
  · intro v z
    have hi : v.val*2^k+z.val < H*2^k := by
      simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using (finProdFinEquiv (v,z)).isLt
    exact (bank_frame lo f r B scratch m ahead (j:=9) (by decide) (by decide)
      (hi.trans_le data.sites)).trans (loads.1 v z)
  · intro p z
    have hi : (slot H Δ p).val*2^k+z.val < (H*Δ)*2^k := by
      simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using (finProdFinEquiv (slot H Δ p,z)).isLt
    exact (bank_frame lo f r B scratch m ahead (j:=10) (by decide) (by decide)
      (hi.trans_le data.traffic)).trans (loads.2 p z)

end Hierarchy.DescentMeasuredPriming.Depth

end
end OAI
