import OAI.Computability.BorderVNP.TransmissionJointLiteral

/-! # Reads from the jointly installed physical processor input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins
open Packing.Directory

/-- The free suffix contains both public stripes and the private half-tail, in order. -/
structure JointRoom (D : Packing.Directory.Layout) (start a : ℕ) (boot geom : GeometryAdvice.Stripe) : Prop where
  /-- The actual padded literal has the directory width. -/
  literal : start+a = D.literal
  /-- Boot fields follow the parsed literal and its single distributed advice bit. -/
  bootStart : start ≤ boot.offset
  /-- The wider startup copy precedes the shared geometry description. -/
  bootEnd : boot.offset+boot.width ≤ geom.offset
  /-- All geometry bits precede the private half-tail. -/
  geomEnd : geom.offset+geom.width ≤ D.literal-D.literal/2

/-- The jointly assigned free bit in an arbitrary real processor-input layout.
Its hypotheses say how the chosen literal was constructed. They apply to both signed
and field-valued processor instruction tables. -/
structure JointImage (D : Packing.Directory.Layout) (start a : ℕ) (boot geom : GeometryAdvice.Stripe)
    (bootBits geomBits : List Bool) (strings : Fin D.entries → Fin D.description → Bool)
    (team : ℕ) {L : Pins.Layout} (F : Pins.ProcessorFields L) : Prop where
  /-- The ordered, disjoint physical regions. -/
  room : JointRoom D start a boot geom
  /-- All slots in the free suffix contain their constructed value. -/
  free (j : Fin L.processors) {addr : ℕ} (lo : start ≤ addr) (hi : addr < D.literal) :
    (F.literal j)[addr]? = some (D.literalBit (fun _ => jointHead boot geom bootBits geomBits)
      strings team j.val addr)

section Image
variable {D : Packing.Directory.Layout} {start a w team : ℕ} {boot geom : GeometryAdvice.Stripe}
    {bootBits geomBits : List Bool} {strings : Fin D.entries → Fin D.description → Bool}
    {L : Pins.Layout} {F : Pins.ProcessorFields L}

/-- The installed literal contains the serialized bit of either stripe at the true
processor index and remainder. This proof covers both copies using their actual
position relative to the two neighboring regions. -/
theorem JointImage.stripe_get (im : JointImage D start a boot geom bootBits geomBits strings team F) (first : Bool)
    (target : GeometryAdvice.Stripe) (xs : List Bool)
    (pick : if first then target = boot ∧ xs = bootBits else target = geom ∧ xs = geomBits)
    (pos : 0 < target.width) (cap : xs.length ≤ L.processors*target.width) (i : Fin xs.length) :
    let p : Fin L.processors := ⟨i.val/target.width,(Nat.div_lt_iff_lt_mul pos).mpr (i.isLt.trans_le cap)⟩
    (F.literal p)[target.offset+i.val%target.width]? = some xs[i.val] := by
  intro p
  have hr := Nat.mod_lt i.val pos
  have idx : p.val*target.width+(target.offset+i.val%target.width-target.offset) = i.val := by
    dsimp only [p]
    rw [Nat.add_sub_cancel_left,Nat.mul_comm,Nat.div_add_mod]
  have inSlot := (show target.offset ≤ target.offset+i.val%target.width ∧
    target.offset+i.val%target.width < target.offset+target.width from ⟨by omega,by omega⟩)
  have bs := im.room.bootStart
  have be := im.room.bootEnd
  have ge := im.room.geomEnd
  have ranges : start ≤ target.offset ∧ target.offset+target.width ≤ D.literal-D.literal/2 := by
    cases first <;> simp only [Bool.false_eq_true,ite_false,ite_true] at pick <;> rw [pick.1] <;> omega
  have inHead : target.offset+i.val%target.width < D.literal-D.literal/2 := by omega
  rw [im.free p
    (by omega) (by omega), D.literalBit_head _ _ _ _ _ inHead]
  cases first with
  | false =>
    change target = geom ∧ xs = geomBits at pick
    obtain ⟨rfl,rfl⟩ := pick
    simp only [jointHead,ite_eq_right (by omega : ¬target.offset+i.val%target.width < target.offset),
      ite_eq_left inSlot,idx,List.getElem?_eq_getElem i.isLt,Option.getD_some]
  | true =>
    change target = boot ∧ xs = bootBits at pick
    obtain ⟨rfl,rfl⟩ := pick
    simp only [jointHead,ite_eq_left (by omega : target.offset+i.val%target.width < geom.offset),
      ite_eq_left inSlot,idx,List.getElem?_eq_getElem i.isLt,Option.getD_some]

/-- The bytecode's striped-source address returns the requested actual bit, before any
writes to scratch. This uses the physically wired processor inputs. -/
theorem JointImage.stripe_read (im : JointImage D start a boot geom bootBits geomBits strings team F) (first : Bool)
    (target : GeometryAdvice.Stripe) (xs : List Bool)
    (pick : if first then target = boot ∧ xs = bootBits else target = geom ∧ xs = geomBits)
    (pos : 0 < target.width) (cap : xs.length ≤ L.processors*target.width) (i : Fin xs.length)
    (mem : Memory w) (input : F.ContainsInput mem) :
    mem (target.src L.stride i.val) = DiagonalResidueRAM.word w xs[i.val].toNat := by
  let p : Fin L.processors := ⟨i.val/target.width,(Nat.div_lt_iff_lt_mul pos).mpr (i.isLt.trans_le cap)⟩
  have bit := im.stripe_get first target xs pick pos cap i
  have existsBit : (F.literal p)[target.offset+i.val%target.width]? = some xs[i.val] := bit
  have hj : target.offset+i.val%target.width < L.literal := by
    rw [← F.literal_length p]
    exact List.getElem?_eq_some_iff.mp existsBit |>.choose
  have read := input.literal p ⟨_,hj⟩
  rw [GeometryAdvice.Stripe.src,Nat.add_assoc]
  exact read.trans (by simp only [TeamTapeInputEmit.headerWord,existsBit,Option.getD_some]; rfl)

end Image

variable {pc reg k routines m g R r w a d link n e : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a) (D : Packing.Directory.Layout) (pack : Fin (R+1) → ReferencePacket w d)
variable (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : Fin (R+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)
variable (fit : Fits P lib r w a R link n e)
variable (u : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ib hb sb : ℕ)

local notation "start" => freeStart P lib r w n
local notation "sites" => S.joint D start pack boot geom bootBits geomBits strings
local notation "fields" => Wiring.processorFields (wiring P lib sites d link n e fit) u pin ext ib hb sb
local notation "region" => fun _ : ℕ => jointHead boot geom (bootBits u) (geomBits u)

/-- Every free physical word has the canonical bit, including the final zero-padded
processor in a stripe and the private half-tail. -/
theorem joint_free_at (room : JointRoom D start a boot geom) (j : Fin r) {addr : ℕ}
    (lo : start ≤ addr) (hi : addr < D.literal) :
    ((fields).literal j)[addr]? = some (D.literalBit region strings u.val j.val addr) := by
  have len := room.literal
  let z : Fin a := ⟨addr-start, by omega⟩
  have off : start+z.val = addr := by dsimp only [z]; omega
  have bit := literal_free_get P lib sites link n e fit u j pin ext ib hb sb z
  change ((fields).literal j)[start+z.val]? = some (D.literalBit region strings u.val j.val (start+z.val)) at bit
  rwa [off] at bit

/-- The actual installed signed processor has the joint image. -/
theorem signed_joint_image (room : JointRoom D start a boot geom) :
    JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val (fields) :=
  ⟨room, fun j _ lo hi => joint_free_at P lib S D pack boot geom bootBits geomBits strings fit u pin ext ib hb sb room j lo hi⟩

/-- The installed literal contains the serialized bit of either stripe at the true
processor index and remainder. This proof covers both copies using their actual
position relative to the two neighboring regions. -/
theorem joint_stripe_get (room : JointRoom D start a boot geom) (first : Bool)
    (target : GeometryAdvice.Stripe) (xs : List Bool)
    (pick : if first then target = boot ∧ xs = bootBits u else target = geom ∧ xs = geomBits u)
    (pos : 0 < target.width) (cap : xs.length ≤ r*target.width) (i : Fin xs.length) :
    let p : Fin r := ⟨i.val/target.width,(Nat.div_lt_iff_lt_mul pos).mpr (i.isLt.trans_le cap)⟩
    ((fields).literal p)[target.offset+i.val%target.width]? = some xs[i.val] :=
  (signed_joint_image P lib S D pack boot geom bootBits geomBits strings fit u pin ext ib hb sb room).stripe_get
    first target xs pick pos cap i

/-- The bytecode's striped-source address returns the requested actual bit, before any
writes to scratch. This uses the physically wired processor inputs. -/
theorem joint_stripe_read (room : JointRoom D start a boot geom) (first : Bool)
    (target : GeometryAdvice.Stripe) (xs : List Bool)
    (pick : if first then target = boot ∧ xs = bootBits u else target = geom ∧ xs = geomBits u)
    (pos : 0 < target.width) (cap : xs.length ≤ r*target.width) (i : Fin xs.length)
    (mem : Memory w) (input : (fields).ContainsInput mem) :
    let L := (wiring P lib sites d link n e fit).pinLayout u ib hb sb
    mem (target.src L.stride i.val) = DiagonalResidueRAM.word w xs[i.val].toNat :=
  (signed_joint_image P lib S D pack boot geom bootBits geomBits strings fit u pin ext ib hb sb room).stripe_read
    first target xs pick pos cap i mem input

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
