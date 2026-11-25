import OAI.Computability.BorderVNP.TransmissionReceivedFields

/-! # Readback of the original one-copy site descriptions from the true joint wiring -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Transmission RoutingISA.Pins
open CellSparse.Packet.Source (siteString Delivered)

variable {pc reg k routines m g R r w a d link n e : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a) (D : Packing.Directory.Layout) (pack : Fin (R+1) → ReferencePacket w d)
variable (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : Fin (R+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool) (fit : Fits P lib r w a R link n e)
variable (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
variable (wire : Routing.WireLayout (R+1) r link) (pp lp : ℕ → ℕ × ℕ)
variable (owner : ℕ → Fin (R+1)) (origin stride : ℕ) (H : Fin (R+1) → TeamHistory w)
variable (ib hb sb : Fin (R+1) → ℕ)

local notation "start" => freeStart P lib r w n
local notation "sites" => S.joint D start pack boot geom bootBits geomBits strings
local notation "wired" => wiring P lib sites d link n e fit
local notation "PL" => fun u => Wiring.pinLayout (wired) u (ib u) (hb u) (sb u)
local notation "Transfer" => ReturnedDelivery (wired) pin ext wire D pp lp owner origin stride H PL

/-- A native receipt at every original site's metadata reservation. This directly
retains the field-zero witness from the joint private-source construction, so
private readback only needs the genuine initialized processor literal. -/
theorem joint_private_received (delivery : Transfer) (room : JointRoom D start a boot geom)
    (teams : D.teams = R+1) (tail : 0 < D.literal/2) (short : D.description ≤ D.literal/2)
    (capacity : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2))
    (entry : Fin D.entries) (b : Fin D.description) :
    (H (owner (pp entry).1)).history.val.2.2 (origin+(pp entry).1*stride+(pp entry).2+b.val) =
      Fin.ofNat _ (strings entry b).toNat := by
  obtain ⟨row,mem,j,hj,field,team,proc,off,hc,hs,bit⟩ :=
    D.private_literal_row pp lp (wired).literalHead strings entry b delivery.positive tail short capacity
  let u : Fin (R+1) := ⟨row.team,teams ▸ team⟩
  have count : D.processors = r := (delivery.dimensions u).1
  let p : Fin r := ⟨row.processor,count ▸ proc⟩
  let o : Fin (PL u).literal := ⟨row.offset+j,(delivery.dimensions u).2 ▸ off⟩
  have read := (delivery.receipt row mem j hj u rfl).read
  have src := (delivery.loaded u).literal p o
  change (H u).initial (row.processor*(PL u).stride+(row.offset+j)) =
    TeamTapeInputEmit.headerWord w (((wired).processorFields u pin ext (ib u) (hb u) (sb u)).literal p) (row.offset+j) at src
  have lit := joint_literal_row P lib S D pack boot geom bootBits geomBits strings fit pin ext room u p
    (ib u) (hb u) (sb u)
  rw [lit] at src
  have source : row.sourceBase (PL u)+j = row.processor*(PL u).stride+(row.offset+j) := by
    rw [Packing.Directory.Row.sourceBase,ite_eq_left field,Nat.add_assoc]
  rw [source] at read
  have exactBit : TeamTapeInputEmit.headerWord w
      (List.ofFn (fun x : Fin D.literal => D.literalBit (wired).literalHead strings u p x)) (row.offset+j) =
        Fin.ofNat _ (strings entry b).toNat := by
    simp [TeamTapeInputEmit.headerWord,off,u,p,bit]
  have result := read.trans (src.trans exactBit)
  rw [hc,Nat.add_assoc (origin+(pp entry).1*stride),hs,← Nat.add_assoc (origin+(pp entry).1*stride)] at result
  exact result

/-- The opaque native factor chunk can read its length header and every used factor
bit from the cell's returned physical reservation. -/
theorem joint_sites_delivered (width : ℕ) (fs : Fin D.entries → List CellSparse.Factor)
    (data : ∀ j b, strings j b = siteString width (fs j) b) (delivery : Transfer)
    (room : JointRoom D start a boot geom) (teams : D.teams = R+1)
    (tail : 0 < D.literal/2) (short : D.description ≤ D.literal/2)
    (capacity : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2)) (entry : Fin D.entries) :
    Delivered (description := D.description) (readings (H (owner (pp entry).1)).history.val.2.2)
      (origin+(pp entry).1*stride+(pp entry).2) width (fs entry) := by
  intro b _
  have read := joint_private_received P lib S D pack boot geom bootBits geomBits strings fit pin ext wire pp lp
    owner origin stride H ib hb sb delivery room teams tail short capacity entry b
  change ((H _).history.val.2.2 _).val = _
  rw [read,Fin.val_ofNat,data]
  exact Nat.mod_eq_of_lt ((Bool.toNat_lt _).trans_le (Nat.one_lt_pow delivery.word.ne' (by decide : 1 < 2)))

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
