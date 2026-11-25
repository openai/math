import OAI.Computability.BorderVNP.TransmissionJointInstall
import OAI.Computability.BorderVNP.TransmissionJointPrivate
import OAI.Computability.BorderVNP.FiniteLiteral

/-! # Joint advice for the actual selected field or signed processor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM UniversalMachine RoutingISA RoutingISA.Pins
open private literalRow_eq from OAI.Computability.BorderVNP.TransmissionJointPrivate

variable {pc reg k routines R r w a d link n e : ℕ}
variable (physical : Program) (P : TeamOpcode.Program pc reg k routines) (S : SiteData R r reg k w a)
variable (D : Packing.Directory.Layout) (pack : Fin (R+1) → ReferencePacket w d)
variable (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : Fin (R+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)
variable (fit : fitsWith physical reg k r w a R link n e)
variable (u : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ib hb sb : ℕ)

local notation "start" => freeStartWith physical r k reg w n
local notation "sites" => S.joint D start pack boot geom bootBits geomBits strings
local notation "wired" => wiringWith physical P sites d link n e fit
local notation "fields" => Wiring.processorFields (wired) u pin ext ib hb sb

/-- The real field-valued, or signed, processor with its own program prefix obtains
the same canonical joint image. Its physical prefix length is computed from that program. -/
theorem joint_image_with (room : JointRoom D start a boot geom) :
    JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val (fields) := by
  refine ⟨room, fun j {addr} lo hi => ?_⟩
  have len := room.literal
  let z : Fin a := ⟨addr-start,by omega⟩
  have off : start+z.val = addr := by dsimp only [z]; omega
  have bit := literal_free_getWith physical P sites link n e fit u j pin ext ib hb sb z
  change ((fields).literal j)[start+z.val]? = some (D.literalBit (fun _ =>
    jointHead boot geom (bootBits u) (geomBits u)) strings u.val j.val (start+z.val)) at bit
  rwa [off] at bit

/-- A field processor's private-data directory reads the same literal that contains
the actual weighted program and its signed/field-specific startup parameters. -/
theorem joint_literal_with (room : JointRoom D start a boot geom) (j : Fin r) :
    (fields).literal j = List.ofFn (fun i : Fin D.literal => D.literalBit (wired).literalHead strings u j i) := by
  obtain ⟨pref,len,eq⟩ := literal_splitWith physical P sites link n e fit u j pin ext ib hb sb
  have lf : ((fields).literal j).length = D.literal :=
    (congrArg List.length eq).trans (by rw [List.length_append,List.length_ofFn,len,room.literal])
  apply literalRow_eq (wired) D u j pin ext ib hb sb strings (fields) rfl lf
  intro i hi
  have bs := room.bootStart
  have be := room.bootEnd
  have ge := room.geomEnd
  have im := joint_image_with physical P S D pack boot geom bootBits geomBits strings fit u pin ext ib hb sb room
  exact (im.free j (by omega : start ≤ i.val) i.isLt).trans
    (congrArg some (literalBit_tail D _ _ _ _ _ _ hi))

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
