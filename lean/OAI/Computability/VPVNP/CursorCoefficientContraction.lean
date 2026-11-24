import OAI.Computability.VPVNP.CursorIncidentExtension
import OAI.Computability.VPVNP.RAMSiteInput
import OAI.Computability.VPVNP.PairedFamily

/-!
# Universal coefficients at routed processor sites

A routed site evaluates its input at the selected mask fields. The exact
coefficient identity on sender arrays therefore applies even to a local
argument of a contraction before route ties have been imposed globally.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open BurstRAM PrivateRAM RAMLayout CursorRouting NetworkKernel

variable {n d e w pc regs pubs : ℕ} (D : UniversalMachine.Program)
    (fit : ProcessorInput.Fits D n d (2^e) w)
    (M : Machine w pc regs pubs) (fuel : ℕ) (initial : Word w)
    (hdr : Site d → ProcessorInput.Header) (hw : 4 ≤ w) (hc : 2^d*2^e < 2^w)

/-- Word header at a routed site. The initialization addresses beyond the
network have their usual zero default. -/
def headerAt (i : ℕ) : Word w :=
  if hi : i < 2^d then ProcessorInput.headerWord hw (hdr ⟨i,hi⟩) else 0

theorem headerAt_site (v : Site d) : headerAt hdr hw v.val = ProcessorInput.headerWord hw (hdr v) := by
  simp [headerAt,v.isLt]

/-- Encode a routed site's processor header and incident RAM payloads as the Boolean input to
its local processor. -/
def cursorInput (v : Site d) (out inc : RAMPayload d (2^e) w) : Fin n → Bool :=
  ProcessorInput.encode D n v (hdr v) (decodeIncident v out inc) fit

variable (processor : ∀ (v : Site d) (a : SendArrays d (2^e) w),
  acceptingCount (ProcessorInput.encode D n v (hdr v) (RAMLayout.incidentBits a v) fit) =
    Nat.card (M.IncidentPaths fuel initial (ProcessorInput.headerWord hw (hdr v))
      (by omega) hc v (RAMLayout.incidentBits a v)))

include processor
theorem cursorInput_count (v : Site d) (out inc : RAMPayload d (2^e) w) :
    acceptingCount (cursorInput D fit hdr v out inc) =
      Nat.card (validatorPaths M fuel initial (headerAt hdr hw) (by omega) hc v out inc) := by
  have h := processor v (localExtension v out inc)
  rw [localExtension_incident] at h
  simpa only [cursorInput, validatorPaths, headerAt_site] using h

theorem cursorInput_coeff (v : Site d) (out inc : RAMPayload d (2^e) w) :
    (P n).coeff (pairedExponent (cursorInput D fit hdr v out inc)) =
      (Nat.card (validatorPaths M fuel initial (headerAt hdr hw) (by omega) hc v out inc) : ℤ) := by
  rw [coeff_P, cursorInput_count D fit M fuel initial hdr hw hc processor]

variable [NeZero d]

open scoped Classical in
/-- The integer contraction of the uncompressed cursor network evaluates
the exact natural coefficients of the universal paired polynomial. -/
theorem cursorInput_contract :
    contract (validatorNetwork d e w)
      (factors systemMask (fun v out inc => if ActiveSends v out then
        acceptingCount (cursorInput D fit hdr v out inc) else 0)) =
      Nat.card (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2^d) (headerAt hdr hw))
        (withinCaps (2^d) (2^e))) := by
  rw [contract_ram]
  rw [← validatorPaths_sum M fuel initial (headerAt hdr hw) (by omega : 2 ≤ w) hc]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  exact cursorInput_count D fit M fuel initial hdr hw hc processor v _ _

end CursorNetwork

end VPVNP
end Computability
end OAI
