import OAI.Computability.VPVNP.RAMTapeLiveProcessor
import OAI.Computability.VPVNP.CursorCoefficientContraction
import OAI.Computability.VPVNP.GroupIncidentContraction

/-!
# Contractions of the actual compiled universal coefficients

The processor has one fixed literal program. Its public operand bank is
computed from the length geometry and that program's own prefix. At all
sufficiently large lengths its coefficients replace the live sites in the
original paired contraction, with a single common input fit and word bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveTranscript

open BurstRAM PrivateRAM RAMLayout ProcessorInput RAMTape LiveProgram Filter

variable {p r k n d e w : ℕ}

/-- Exact universal-machine coefficients for every live site's header and incident sends. -/
structure Coefficients (D : UniversalMachine.Program) (M : Machine w p r k)
    (n d e fuel : ℕ) (initial : Word w) : Prop where
  width : 4 ≤ w
  cap : 2^d*2^e < 2^w
  fits : Fits D n d (2^e) w
  count : ∀ (v : Word d) (hdr : Header) (sends : SendArrays d (2^e) w),
    acceptingCount (encode D n v hdr (RAMLayout.incidentBits sends v) fits) =
      Nat.card (M.IncidentPaths fuel initial (headerWord width hdr) (by omega) cap v
        (RAMLayout.incidentBits sends v))

/-- Coefficient identities obtained when the public operand vector fits the current word. -/
def AtGeometry (T : Template p r k) (args : Fin k → InputOperand) (D : UniversalMachine.Program)
    (n d e w lit : ℕ) : Prop :=
  let g : Geometry := ⟨n,d,2^e,w⟩
  (∀ i, (InputOperandStartup.Expr args i).Fits g (2^w)) →
    Coefficients D (T.instantiate w (fun i => Pieces.word g (CounterPublic.actualPrefix D) (args i)))
      n d e (n^10000) (Fin.ofNat (2^w) lit)

theorem eventually_coefficients (T : Template p r k) (args : Fin k → InputOperand)
    (B a b lit : ℕ) (hB : 1 ≤ B) (hb : 0 < b) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, AtGeometry T args (SiteProcessorPorts.machine T args B a b 10000 lit hb) n
      (addressWidth B n) (roundedUp a b n) (CursorBounds.wordBits B n) lit := by
  filter_upwards [SiteProcessorPorts.eventually_machine_count T args B a b lit hB hb hab] with n h
  intro hg
  obtain ⟨fit, site⟩ := h
  obtain ⟨hc,_⟩ := site hg 0 (fun _ => false) (fun _ _ => false, fun _ _ _ => false)
  exact ⟨ProcessorPublic.recordWidth_ge_four _, hc, fit, fun v hdr sends => (site hg v hdr sends).choose_spec⟩

variable {D : UniversalMachine.Program} {M : Machine w p r k} {fuel : ℕ} {initial : Word w}
    (c : Coefficients D M n d e fuel initial)

theorem Coefficients.groups {a h Δ : ℕ} (advice : CutSchedule.Bits a) :
    PairedChain.original (h := h) (Δ := Δ) D c.fits advice =
      ∑ cuts : ChainAssignments.AllCuts h Δ, ∏ j : Fin (2^(h+1)), Nat.card
        (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2^d)
          (ChainAssignments.liveHeader (d := d) c.width advice cuts j)) (withinCaps (2^d) (2^e))) :=
  ChainAssignments.original_eq_incident_counts D c.fits advice M fuel initial c.width c.cap c.count

open CursorNetwork CursorRouting NetworkKernel in
theorem Coefficients.localPolynomial (hdr : Site d → Header) (v : Site d) (out inc : RAMPayload d (2^e) w) :
    (P n).coeff (pairedExponent (cursorInput D c.fits hdr v out inc)) =
      (Nat.card (validatorPaths M fuel initial (headerAt hdr c.width) (by have := c.width; omega)
        c.cap v out inc) : ℤ) :=
  cursorInput_coeff D c.fits M fuel initial hdr c.width c.cap (fun v => c.count v (hdr v)) v out inc

open CursorNetwork CursorRouting NetworkKernel in
open scoped Classical in
theorem Coefficients.routed [NeZero d] (hdr : Site d → Header) :
    contract (validatorNetwork d e w) (factors systemMask (fun v out inc => if ActiveSends v out then
      acceptingCount (cursorInput D c.fits hdr v out inc) else 0)) =
      Nat.card (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2^d) (headerAt hdr c.width))
        (withinCaps (2^d) (2^e))) :=
  cursorInput_contract D c.fits M fuel initial hdr c.width c.cap (fun v => c.count v (hdr v))

end LiveTranscript

end VPVNP
end Computability
end OAI
