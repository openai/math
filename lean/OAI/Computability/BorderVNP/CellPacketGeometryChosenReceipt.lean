import OAI.Computability.BorderVNP.CellPacketGeometrySignedReceipt
import OAI.Computability.BorderVNP.TransmissionJointProgram

/-! # The original private tape at its emitted address on the fixed interpreter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Transmission RoutingISA.Pins
open CellSparse Packet CellPacketGeometry.History Packing Packing.Inherited Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical CellPacketGeometry.History.Native

section
variable {pc reg k routines R r w a d link n e : ℕ}
variable (program : UniversalMachine.Program) (P : TeamOpcode.Program pc reg k routines)
variable (S : SiteData R r reg k w a) (D : Packing.Directory.Layout) (pack : Fin (R+1) → ReferencePacket w d)
variable (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : Fin (R+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool) (fit : fitsWith program reg k r w a R link n e)
variable (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
variable (wire : Routing.WireLayout (R+1) r link) (pp lp : ℕ → ℕ × ℕ)
variable (owner : ℕ → Fin (R+1)) (origin stride : ℕ) (H : Fin (R+1) → TeamHistory w)
variable (ib hb sb : Fin (R+1) → ℕ)

local notation "start" => freeStartWith program r k reg w n
local notation "sites" => S.joint D start pack boot geom bootBits geomBits strings
local notation "wired" => wiringWith program P sites d link n e fit
local notation "PL" => fun u => Wiring.pinLayout (wired) u (ib u) (hb u) (sb u)
local notation "Transfer" => ReturnedDelivery (wired) pin ext wire D pp lp owner origin stride H PL

/-- A protected private row is copied from the installed source literal on its
actual local or remote route. The unused head of that literal is unconstrained. -/
theorem joint_private_received_of_row (delivery : Transfer)
    (literal : ∀ (u : Fin (R+1)) (p : Fin r),
      ((wired).processorFields u pin ext (ib u) (hb u) (sb u)).literal p =
        List.ofFn (fun i : Fin D.literal => D.literalBit (wired).literalHead strings u p i))
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
  have lit := literal u p
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


/-- Every bit of the installed one-copy site description, including its
tally suffix, is present at the actual receiver of this fixed processor
program. The sorter, packet prefix and literal offset belong to that same
program. -/
theorem joint_private_received_with (delivery : Transfer) (room : JointRoom D start a boot geom)
    (teams : D.teams = R+1) (tail : 0 < D.literal/2) (short : D.description ≤ D.literal/2)
    (capacity : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2))
    (entry : Fin D.entries) (b : Fin D.description) :
    (H (owner (pp entry).1)).history.val.2.2 (origin+(pp entry).1*stride+(pp entry).2+b.val) =
      Fin.ofNat _ (strings entry b).toNat := by
  exact joint_private_received_of_row program P S D pack boot geom bootBits geomBits strings fit
    pin ext wire pp lp owner origin stride H ib hb sb delivery (fun u p =>
      joint_literal_with program P S D pack boot geom bootBits geomBits strings fit u pin ext (ib u) (hb u) (sb u) room p)
    teams tail short capacity entry b

end

section
variable {pc reg k routines g R r w a d link n e : ℕ}
variable (program : UniversalMachine.Program) (P : TeamOpcode.Program pc reg k routines)
variable (S : SiteData R r reg k w a) (dir : Packing.Directory.Layout) (pack : Fin (R+1) → ReferencePacket w d)
variable (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : Fin (R+1) → List Bool)
variable (strings : Fin dir.entries → Fin dir.description → Bool)
variable (fit : fitsWith program reg k r w a R link n e) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
variable (wire : Routing.WireLayout (R+1) r link) (lp : ℕ → ℕ × ℕ) (team : ℕ → Fin (R+1))
variable (arena stride : ℕ) (H : Fin (R+1) → TeamHistory w) (ib hb sb : Fin (R+1) → ℕ)

local notation "start" => freeStartWith program r k reg w n
local notation3 "wired" => wiringWith program P (S.joint dir start pack boot geom bootBits geomBits strings) d link n e fit
local notation3 "PL" => fun u => Wiring.pinLayout (wired) u (ib u) (hb u) (sb u)

variable {D sites edges ports C levels ownerBits L : ℕ} {Port σ O : Type} [Fintype Port] [Fintype σ] {bits : Port → ℕ}
    (N : Network D Port bits) (cell : N.Site → Fin C) (state : N.Site → Site)
    (sid : N.Site ↪ Fin sites) (edgeID : N.Edge ↪ Fin edges) (portID : Port ↪ Fin ports)
    (F : Fields sites edges ports C levels ownerBits w σ) (x : σ → Bool)
    (physical : Represents N cell (fun v => (state v).size) sid edgeID portID F x)
    (codes : ∀ c, (F.cells c).val=c.val)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c<2^w)
    (boxes : Fin sites → List (Source.Box O)) (entry : Fin dir.entries → Fin sites)
    (host : Fin dir.entries → N.Site) (hosts : ∀ i, entry i=sid (host i))
    (live : Fin L → Port) (frame origin gap digits : ℕ) (before placed : ℕ → ℕ)

local notation3 "l" => RoutingOutputs.privateLayout frame origin edges C dir.entries dir.description gap
local notation3 "pp" => Packing.Directory.ISA.placement placed (l).raw

include physical codes sizeFit hosts in
/-- Every charged original bit is delivered at the address selected by the
actual public pointer circuit, on this exact receiving team. These are the
original factor bytes and report sidecar even when the ensuing private
validator has zero value. -/
theorem chosen_descriptor_bits (geo : RoutingOutputs.Image F (sid ∘ host) (portID ∘ live) x origin before)
    (image : (l).Image before dir.entries placed) (placedFit : (l).Fits w before)
    (delivery : ReturnedDelivery (wired) pin ext wire dir (pp) lp team arena stride H PL)
    (jointRoom : JointRoom dir start a boot geom) (teams : dir.teams=R+1)
    (tail : 0 < dir.literal/2) (short : dir.description ≤ dir.literal/2)
    (volume : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2))
    (j : Fin dir.entries)
    (address : opaquePointer (fun c => arena+c*stride) (fun c => before ((l).supplied+c)) ((l).owner before)
      gap dir.description j < 2^w) (b : Fin dir.description) :
    (readings (H (team (cell (host j)).val)).history.val.2.2)
      ((ParseBatchSort.value fun t => (SignedFields.frame F boxes entry arena stride gap dir.description g digits).eval
        x (.inr j,t))+b.val) = (strings j b).toNat := by
  have facts := geo.placed N cell (fun v => (state v).size) sid edgeID portID F physical codes sizeFit host live origin before
  have owns : (l).owner before j.val = (cell (host j)).val := by
    simpa only [RoutingOutputs.privateLayout,PrivatePlacement.Layout.owner,Packing.Directory.ISA.placement,
      Nat.mul_comm j.val 2] using congrArg Prod.fst (facts.1 j)
  rw [SignedFields.pointer_opaque F N cell (fun v => (state v).size) sid edgeID portID physical codes sizeFit
    boxes entry host hosts live frame origin arena stride gap dir.description before g digits geo placedFit j address]
  have coords := opaquePlacement (l) image placedFit j
  change (pp) j = _ at coords
  have received := joint_private_received_with program P S dir pack boot geom bootBits geomBits strings fit pin ext wire
    (pp) lp team arena stride H ib hb sb delivery jointRoom teams tail short volume j b
  have stored := congrArg Fin.val received
  rw [Fin.val_ofNat,Nat.mod_eq_of_lt ((Bool.toNat_lt _).trans_le
    (Nat.one_lt_pow delivery.word.ne' (by decide : 1 < 2)))] at stored
  have owner : ((pp) j.val).1 = (cell (host j)).val := (congrArg Prod.fst coords).trans owns
  rw [owner] at stored
  simpa only [coords,owns,opaquePointer,readings,show (l).gap=gap from rfl,
    show (l).desc=dir.description from rfl,Nat.add_assoc] using stored

end
end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
