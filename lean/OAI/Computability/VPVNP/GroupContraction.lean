import OAI.Computability.VPVNP.ChainAssignments
import OAI.Computability.VPVNP.RAMValidatorPaths

/-! # Replacing live groups by native RAM computations

Each cut choice fixes a group's header memory. The sum over its communication
bits is then exactly the number of accepting RAM paths. The site-prefix
compiler supplies the local path-count identity; the regrouping works even
when a particular choice of incident messages is malformed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ChainAssignments

open BurstRAM BurstRAM.PrivateRAM RAMLayout
open scoped Classical

variable {n a h Δ d e w pc regs pubs : ℕ}

/-- External memory at a live group is initialized with its actual four-bit
headers. Addresses beyond the group receive the RAM's zero default. -/
def liveHeader (hw : 4 ≤ w) (advice : CutSchedule.Bits a) (cuts : AllCuts h Δ)
    (j : Fin (2^(h+1))) (addr : ℕ) : Word w :=
  if hv : addr < 2^d then ProcessorInput.headerWord hw (physicalHeader advice cuts j ⟨addr,hv⟩)
  else 0

/-- The full contraction with the site computations for each group replaced
by one computation of its RAM program, with the same address and cut data. -/
theorem original_eq_group_counts (p : UniversalMachine.Program)
    (hf : ProcessorInput.Fits p n d (2^e) w) (advice : CutSchedule.Bits a)
    (M : Machine w pc regs pubs) (fuel : ℕ) (initial : Word w)
    (hw : 4 ≤ w) (hc : 2^d * 2^e < 2^w)
    (processor : ∀ (v : Fin (2^d)) (hdr : ProcessorInput.Header) inc,
      acceptingCount (ProcessorInput.encode p n v hdr inc hf) =
        Nat.card (M.IncidentPaths fuel initial (ProcessorInput.headerWord hw hdr)
          (by omega) hc v inc)) :
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
  unfold physicalInput
  rw [processor]
  have hinc : BurstRAM.incidentBits (bits j) v =
      (fun u => (assignmentEquiv d (2^e) w (bits j)).val (v,(offset d (2^e) w).symm u)) := by
    funext u
    change (((assignmentEquiv d (2^e) w) ((sendArraysEquiv d (2^e) w).symm ((sendArraysEquiv d (2^e) w) (bits j)))).val _ = _)
    rw [Equiv.symm_apply_apply]
  simp [hinc, liveHeader, v.isLt]

end ChainAssignments

end VPVNP
end Computability
end OAI
