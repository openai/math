import OAI.Computability.BorderVNP.RoutingISASignedFrame
import OAI.Computability.BorderVNP.TransmissionChosenPhysical

/-! # Placing the shared frame and fixed Fourier-entry pointer in actual signed site literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM TeamContraction.ProcessorSlots

variable {R r reg w a d : ℕ}

/-- Initialize the non-startup public operand positions of every actual
processor, retaining its independently chosen program and starting state. -/
noncomputable def withOrdinary (S : SiteData R r reg 32 w a) (l : Fin (R+1) → Layout)
    (A : StartupArena) (cable plan u v gates : Fin (R+1) → ℕ) : SiteData R r reg 32 w a :=
  { S with publicWords := fun t ↦ (l t).ordinary A (cable t) (plan t) (u t) (v t) (gates t) (S.publicWords t) }

/-- In the real combined site installation the public bank still contains the
entry address chosen by the reader allocation and the complete routing and call
pointers. Installing private literals and the two separate advice stripes cannot
change any of these six public words. -/
theorem joint_ordinary (S : SiteData R r reg 32 w a) (l : Fin (R+1) → Layout)
    (A : StartupArena) (cable plan u v gates : Fin (R+1) → ℕ)
    (B : Fin (R+1) → PacketOperands) (D : Packing.Directory.Layout) (start : ℕ)
    (p : Fin (R+1) → ReferencePacket w d) (boot geom : GeometryAdvice.Stripe)
    (bootBits geomBits : Fin (R+1) → List Bool) (strings : Fin D.entries → Fin D.description → Bool)
    (t : Fin (R+1)) :
    let trueSites := ((withOrdinary S l A cable plan u v gates).withOperands B).joint D start p boot geom bootBits geomBits strings
    let pub := trueSites.publicWords t
    pub 7=TeamTapeInputEmit.word w (cable t) ∧ pub 9=TeamTapeInputEmit.word w A.next ∧
      pub 13=TeamTapeInputEmit.word w (l t).cube.records ∧ pub 15=TeamTapeInputEmit.word w (l t).before.limit ∧
      pub 16=TeamTapeInputEmit.word w (l t).cube.cells ∧ pub 20=TeamTapeInputEmit.word w ((l t).entry w (u t) (v t) (gates t)) :=
  (l t).ordinary_receipts A (B t) (cable t) (plan t) (u t) (v t) (gates t) (S.publicWords t)

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
