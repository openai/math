import OAI.Computability.BorderVNP.DiagonalNativeTimedScaleModes
import OAI.Computability.BorderVNP.TransmissionStartupArena

/-! # Installed broadcast operands from the physical timed startup arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator TeamSite TeamScales
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators

/-- The addresses consumed by the unit branch and the common header reader in a
contiguous physical arena. The live and substituted index each have a full pin region. -/
def StartupArena.unitAddresses {w d : ℕ} (A : StartupArena) (off : ℕ) (p : ReferencePacket w d) : UnitAddresses :=
  ⟨A.header,A.broadcastBase,A.ibase,A.hbase,A.dense+p.offset,⟨off,A.copied,A.dense⟩⟩

/-- The physical input precedes all scratch regions. The literal length includes
the executable prefix of the actual timed machine and its whole free suffix. -/
noncomputable def programArena (physical : UniversalMachine.Program)
    (R r w n free link header copied : ℕ) : StartupArena :=
  ⟨R+1,r,entryLiteral physical (w+1) n (prefixCapacity r 32 64 w n+1+free),link,header,copied⟩

/-- The true allocated public word bank satisfies all eight readout conditions on
the actual wiring. This includes the advised reference offset and disjoint copies. -/
theorem fitted_programArena {pc routines R r w a d link n e : ℕ}
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 routines)
    (S : SiteData R r 64 32 w a) (fit : fitsWith physical 64 32 r w a R link n e)
    (header copied : ℕ) (u : Fin (R+1)) (p : ReferencePacket w d) (extra : Arg → Word w)
    (three : 2 < R+1) (hdr : 0 < header) (cap : header ≤ r*link)
    (length : p.bits.length ≤ copied) (copies : copied ≤ r) :
    let A := programArena physical R r w n a link header copied
    let off := adviceOffsetWith physical r 32 64 w n
    let B := A.operands u off p
    let G := wiringWith physical P S d link n e fit
    A.next < 2^w → (A.unitAddresses off p).Fitted G u p (B.bank extra) off := by
  intro A off B G ceiling
  have pos := hdr.trans_le cap
  have slot : off < A.literal := by
    dsimp [A,off,programArena,adviceOffsetWith,entryLiteral]
    omega
  have all := A.fits u off p three (Nat.pos_of_mul_pos_right pos) ((Nat.zero_le _).trans_lt slot)
    (Nat.pos_of_mul_pos_left pos) hdr (Nat.mul_comm r link ▸ cap) slot length copies ceiling
  have frame : ((B.bank extra) 0).val = A.frame := B.frameBase_word extra all.1
  constructor
  · exact B.packetFrame extra all.1
  · rw [frame]; exact all.2.1
  · rw [frame]; exact all.2.2.1
  · rw [frame]; exact all.2.2.2.1
  · rfl
  · exact length
  · rfl
  · left
    change A.dense+p.offset+d ≤ A.dense+copied
    rw [p.bits_length] at length
    omega

variable {Q Γ : Type} [Fintype Q] {m g r n R w e d : ℕ} {α ξ : ℝ}
variable (eval : Code) (lib : Fin 8 → Macro Q Γ m g) (mark : Fin 8 → Γ)
variable (geo : Scale (TimedProcessor.machine (withStartup eval).program lib mark)
  ((withStartup eval).slots+1) 64 32 α ξ r n R w e)

/-- The exact wired native decomposition on allocated scalar operands, for
arbitrary evaluator fields, private data literals, initial registers and live pins. -/
def AllocatedPacketModes (header copied : ℕ) (pack : Fin (R+1) → ReferencePacket w d) : Prop :=
  let P := (withStartup eval).program
  let physical := TimedProcessor.machine P lib mark
  let free := freeWidth physical α 32 64 r w n
  let A := programArena physical R r w n free (link ξ (R+1) n) header copied
  let off := adviceOffsetWith physical r 32 64 w n
  let args := fun u => A.unitAddresses off (pack u)
  ∀ (extra : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (fields : Fin (R+1) → Fin r → Fin free → Bool) (pin : Fin d → Bool),
    let pub := fun u => (A.operands u off (pack u)).bank (extra u)
    let S := TimedProcessor.scaleData P lib mark geo pub reg (fun _ _ => false) fields
    let G := wiringWith physical P (S.withPacket pack) d (link ξ (R+1) n) n e geo.fits
    Diagonal.signedContraction G.slot pin =
      (if pin=(pack 0).reference then 1 else 0) +
      ∑ ext, ∏ u, positiveMaskedNativeValue G eval (TeamSiteEvents.macros lib (n^25+1))
        pub reg args pin (ticks ξ r n) (width n (1/2)) (n^25) ext u

/-- Instantiate the true bank and disjoint addressed ranges on the timed scale. -/
theorem PacketModesAtScale.allocated (modes : PacketModesAtScale eval lib mark geo)
    (header copied : ℕ) (pack : Fin (R+1) → ReferencePacket w d)
    (three : 2 < R+1) (hdr : 0 < header) (cap : header ≤ r*link ξ (R+1) n)
    (length : ∀ u, (pack u).bits.length ≤ copied) (copies : copied ≤ r) :
    let physical := TimedProcessor.machine (withStartup eval).program lib mark
    let free := freeWidth physical α 32 64 r w n
    let A := programArena physical R r w n free (link ξ (R+1) n) header copied
    A.next < 2^w → AllocatedPacketModes eval lib mark geo header copied pack := by
  intro physical free A ceiling extra reg fields pin pub S G
  let off := adviceOffsetWith physical r 32 64 w n
  let args := fun u => A.unitAddresses off (pack u)
  apply modes pub reg (fun _ _ => false) fields pack args pin
  intro u
  exact fitted_programArena physical (withStartup eval).program (S.withPacket pack) geo.fits
    header copied u (pack u) (extra u) three hdr cap (length u) copies ceiling

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
