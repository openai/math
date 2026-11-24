import OAI.Computability.VPVNP.GroupContraction

/-!
# Summing the compiled processor over the live groups' actual shared bits

At each site the original polynomial contraction uses the bit vector
obtained from one sender assignment. This identity only needs the
coefficient formula on those vectors, including the clamps at the two ends.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ChainAssignments

open BurstRAM PrivateRAM RAMLayout

variable {n a h Δ d e w pc regs pubs : ℕ}

theorem original_eq_incident_counts (p : UniversalMachine.Program)
    (hf : ProcessorInput.Fits p n d (2^e) w) (advice : CutSchedule.Bits a)
    (M : Machine w pc regs pubs) (fuel : ℕ) (initial : Word w)
    (hw : 4 ≤ w) (hc : 2^d*2^e < 2^w)
    (processor : ∀ (v : Fin (2^d)) (hdr : ProcessorInput.Header) (sends : SendArrays d (2^e) w),
      acceptingCount (ProcessorInput.encode p n v hdr (RAMLayout.incidentBits sends v) hf) =
        Nat.card (M.IncidentPaths fuel initial (ProcessorInput.headerWord hw hdr)
          (by omega) hc v (RAMLayout.incidentBits sends v))) :
    PairedChain.original (h := h) (Δ := Δ) p hf advice =
      ∑ cuts : AllCuts h Δ, ∏ j : Fin (2^(h+1)), Nat.card
        (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2^d)
          (liveHeader (d := d) hw advice cuts j)) (withinCaps (2^d) (2^e))) := by
  rw [← unpaired_eq_original, unpaired, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro cuts _
  simp_rw [M.parsimoniousIncidentPaths fuel initial _ (by omega : 2 ≤ w) hc]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro bits _
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro v _
  let sends := sendArraysEquiv d (2^e) w (bits j)
  have inc : RAMLayout.incidentBits sends v =
      (fun u => (assignmentEquiv d (2^e) w (bits j)).val (v,(offset d (2^e) w).symm u)) := by
    unfold RAMLayout.incidentBits incidentEquiv sends
    simp
  have eqn := processor v (physicalHeader advice cuts j v) sends
  rw [inc] at eqn
  unfold physicalInput
  rw [eqn]
  have hinc : BurstRAM.incidentBits (bits j) v =
      (fun u => (assignmentEquiv d (2^e) w (bits j)).val (v,(offset d (2^e) w).symm u)) := by
    simpa only [BurstRAM.incidentBits] using inc
  simp [hinc, liveHeader, v.isLt]

end ChainAssignments

end VPVNP
end Computability
end OAI
