import OAI.Computability.BorderVNP.PackedRoutingPlaced
import OAI.Computability.BorderVNP.TransmissionReceivedPrivate
import OAI.Computability.BorderVNP.CellPacketSiteTail

/-! # The physical read address of an opaque cell-packet box

The private placement pass writes a relative offset for each original row.
Frame 72 supplies its owning cell's receive-bank base, while frame 64
supplies the native row. The received literal occupies that absolute address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open Packing Packing.Directory RoutingISA

/-- Absolute pointer read by the cell geometry for original description row `j`. -/
def opaquePointer (bank supply owners : ℕ → ℕ) (gap description j : ℕ) : ℕ :=
  bank (owners j) + supply (owners j) + gap + PrivatePlacement.prefixCounts owners description j (owners j)

/-- Read the current destination cell and relative placement from frame 64 and
its two-word receive-bank directory from frame 72. -/
def opaqueFrameSlot (mem : ℕ → ℕ) (frame j : ℕ) : ℕ :=
  let p := ISA.placement mem (mem (frame+64)) j
  mem (mem (frame+72)+2*p.1+1) + p.2

/-- The completed native pass writes both coordinates of each real description
row. Its relative offset is the supplied count, report gap, and preceding widths. -/
theorem opaquePlacement (l : PrivatePlacement.Layout) {w : ℕ} {before placed : ℕ → ℕ}
    (image : l.Image before l.entries placed) (fit : l.Fits w before) (j : Fin l.entries) :
    ISA.placement placed l.raw j =
      (l.owner before j, before (l.supplied+l.owner before j)+l.gap+
        PrivatePlacement.prefixCounts (l.owner before) l.desc j (l.owner before j)) := by
  exact Prod.ext (by simpa only [ISA.placement,Nat.mul_comm j.val 2] using image.owner_eq fit j.isLt)
    (by simpa only [ISA.placement,Nat.mul_comm j.val 2] using image.slots j.val j.isLt)

/-- Reading both physical frame pointers agrees with the address computed from
the bank layout and prefix of original rows. Only the two words of this real
placement row and the indicated receive-bank word are used. -/
theorem opaqueFrameSlot_eq (l : PrivatePlacement.Layout) {w : ℕ} (before placed mem : ℕ → ℕ)
    (image : l.Image before l.entries placed) (fit : l.Fits w before)
    (bank supply : ℕ → ℕ) (j : Fin l.entries) (ptr : mem (l.frame+64) = l.raw)
    (row : ISA.placement mem l.raw j = ISA.placement placed l.raw j)
    (recv : mem (mem (l.frame+72)+2*(l.owner before j)+1) = bank (l.owner before j))
    (sup : before (l.supplied+l.owner before j) = supply (l.owner before j)) :
    opaqueFrameSlot mem l.frame j = opaquePointer bank supply (l.owner before) l.gap l.desc j := by
  simp only [opaqueFrameSlot,ptr,row,opaquePlacement l image fit j,recv,sup,opaquePointer]
  ac_rfl

open Crossing Packing.CellAddresses

/-- The same pointer in the compact mathematical cell bank. The ordered
reservation consists of supplied network words, the report gap, and originals. -/
theorem opaquePointer_eq_bank {D C m n entries : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (origin : Fin entries → N.Site) (bank supply owners : ℕ → ℕ) (gap desc : ℕ)
    (names : ∀ j : Fin entries, owners j.val = (cell (origin j)).val)
    (count : ∀ c : Fin C, supply c.val = suppliedSize N cell c) (j : Fin entries) :
    let sc := Sum.elim (fun a : PrivateBank.SuppliedWord N cell => a.1) (id : Fin C → Fin C)
    let sw := Sum.elim (PrivateBank.supplyWidth N cell) (fun _ : Fin C => gap)
    let si := PrivateBank.reserveID (C := C) (PrivateBank.suppliedID N cell edgeID portID)
    opaquePointer bank supply owners gap desc j =
      bank (cell (origin j)).val + DataSlabs.base (Sum.elim sc (cell ∘ origin))
        (PrivateBank.numbered si) (Sum.elim sw (fun _ => desc)) (.inr j) := by
  intro sc sw si
  rw [PrivateBank.base_private sc (cell ∘ origin) si sw desc owners names j]
  rw [PrivateBank.reservedSize,PrivateBank.dataSlabs_size]
  simp only [opaquePointer,names,count,Function.comp_apply,Nat.add_assoc]

end CellPacketGeometry.History

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA CellPacketGeometry.History

variable {D s m n C d k w J A : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) (F : Fields s m n C d k w σ) {x : σ → Bool}
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (original : Fin J → N.Site) (live : Fin A → P) (frame origin desc gap : ℕ)
    (before placed mem : ℕ → ℕ)
local notation3 "l" => privateLayout frame origin m C J desc gap

include net code fit in
/-- Readback of the absolute opaque address using the physical network image.
The true owner and the supplied-word count come from the exported address
frame. The only post-placement words used are the row pair and bank pointer. -/
theorem Image.opaqueFrameSlot (geo : Image F (siteID ∘ original) (portID ∘ live) x origin before)
    (image : (l).Image before J placed) (room : (l).Fits w before)
    (bank : Fin C → ℕ) (j : Fin J) (ptr : mem (frame+64)=(l).raw)
    (row : Directory.ISA.placement mem (l).raw j = Directory.ISA.placement placed (l).raw j)
    (recv : mem (mem (frame+72)+2*(cell (original j)).val+1) = bank (cell (original j))) :
    CellPacketGeometry.History.opaqueFrameSlot mem frame j =
      bank (cell (original j)) + suppliedSize N cell (cell (original j)) + gap +
        PrivatePlacement.prefixCounts ((l).owner before) desc j (cell (original j)).val := by
  have facts := geo.placed N cell aux siteID edgeID portID F net code fit original live origin before
  have owns : (l).owner before j.val = (cell (original j)).val := by
    simpa only [privateLayout,PrivatePlacement.Layout.owner,Directory.ISA.placement,Nat.mul_comm j.val 2]
      using congrArg Prod.fst (facts.1 j)
  have count : before ((l).supplied+(cell (original j)).val) = suppliedSize N cell (cell (original j)) := by
    simpa only [privateLayout,PrivatePlacement.Layout.supplied,bases,Nat.mul_comm 2 m]
      using facts.2.1 (cell (original j))
  simp only [CellPacketGeometry.History.opaqueFrameSlot,ptr,row,opaquePlacement (l) image room j,owns,count,recv]
  change bank _ + (suppliedSize N cell _ + gap + _) = _
  ac_rfl

end Packing.RoutingOutputs

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Transmission RoutingISA.Pins
open CellSparse Packet CellPacketGeometry.History

variable {pc reg k routines m g R r w a d link n e : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a) (D : Packing.Directory.Layout) (pack : Fin (R+1) → ReferencePacket w d)
variable (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : Fin (R+1) → List Bool)
variable (header cap : ℕ) (fs : Fin D.entries → List Factor) (tally : Fin D.entries → List Bool)
variable (fit : Fits P lib r w a R link n e) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
variable (wire : Routing.WireLayout (R+1) r link) (lp : ℕ → ℕ × ℕ) (team : ℕ → Fin (R+1))
variable (origin stride : ℕ) (H : Fin (R+1) → TeamHistory w) (ib hb sb : Fin (R+1) → ℕ)

local notation3 "strings" => fun j : Fin D.entries => Source.siteWithTally (description := D.description) header cap (fs j) (tally j)
local notation3 "start" => freeStart P lib r w n
local notation3 "wired" => wiring P lib (S.joint D start pack boot geom bootBits geomBits strings) d link n e fit
local notation3 "PL" => fun u => Wiring.pinLayout (wired) u (ib u) (hb u) (sb u)

variable (l : PrivatePlacement.Layout) (before placed : ℕ → ℕ)
local notation3 "pp" => Packing.Directory.ISA.placement placed l.raw

/-- The true joint processor literal, including its separate tally suffix, is
received at exactly the pointer computed by the history geometry. The readback
follows the protected local copy or checked remote relay of the native directory. -/
theorem joint_opaquePointer_delivered (image : l.Image before l.entries placed) (placedFit : l.Fits w before)
    (entries : l.entries = D.entries) (desc : l.desc = D.description)
    (delivery : ReturnedDelivery (wired) pin ext wire D (pp) lp team origin stride H PL)
    (room : JointRoom D start a boot geom) (teams : D.teams = R+1)
    (tail : 0 < D.literal/2) (short : D.description ≤ D.literal/2)
    (volume : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2))
    (j : Fin D.entries) (bodyRoom : (Source.boxBody (fs j)).length ≤ cap)
    (tallyRoom : header+cap+(tally j).length ≤ D.description) :
    Source.Delivered (description := D.description) (readings (H (team (l.owner before j))).history.val.2.2)
      (opaquePointer (fun c => origin+c*stride) (fun c => before (l.supplied+c)) (l.owner before)
        l.gap D.description j) header (fs j) := by
  have coords := opaquePlacement l image placedFit (Fin.cast entries.symm j)
  change (pp) j = _ at coords
  apply (Source.siteWithTally_read _ _ header cap (fs j) (tally j) bodyRoom tallyRoom ?_).1
  intro b
  have bit := joint_private_received P lib S D pack boot geom bootBits geomBits strings fit pin ext wire
    (pp) lp team origin stride H ib hb sb delivery room teams tail short volume j b
  have ownerEq : ((pp) j).1 = l.owner before j := congrArg Prod.fst coords
  rw [ownerEq] at bit
  have word := congrArg Fin.val bit
  simp only [Fin.val_ofNat,Nat.mod_eq_of_lt ((Bool.toNat_lt _).trans_le
    (Nat.one_lt_pow delivery.word.ne' (by decide : 1 < 2)))] at word
  simpa only [coords,Fin.val_cast,desc,opaquePointer,readings,Nat.add_assoc] using word

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
