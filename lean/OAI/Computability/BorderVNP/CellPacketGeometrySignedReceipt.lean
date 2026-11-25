import OAI.Computability.BorderVNP.CellPacketGeometrySignedMetadata
import OAI.Computability.BorderVNP.CellPacketGeometryOpaqueDelivery

/-! # The signed descriptor reads the original body received by the native processor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Transmission RoutingISA.Pins
open CellSparse Packet CellPacketGeometry.History Packing Packing.Inherited Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical CellPacketGeometry.History.Native

variable {pc reg k routines arity g R r w a d link n e : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ arity g)
variable (S : SiteData R r reg k w a) (dir : Packing.Directory.Layout) (pack : Fin (R+1) → ReferencePacket w d)
variable (boot geom : GeometryAdvice.Stripe) (bootBits geomBits : Fin (R+1) → List Bool)
variable (header cap : ℕ) (fs : Fin dir.entries → List Factor) (tally : Fin dir.entries → List Bool)
variable (fit : Fits P lib r w a R link n e) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
variable (wire : Routing.WireLayout (R+1) r link) (lp : ℕ → ℕ × ℕ) (team : ℕ → Fin (R+1))
variable (arena stride : ℕ) (H : Fin (R+1) → TeamHistory w) (ib hb sb : Fin (R+1) → ℕ)

local notation3 "strings" => fun j : Fin dir.entries => Source.siteWithTally (description := dir.description) header cap (fs j) (tally j)
local notation "start" => freeStart P lib r w n
local notation3 "wired" => wiring P lib (S.joint dir start pack boot geom bootBits geomBits strings) d link n e fit
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
/-- The original pointer pin of the shared signed frame addresses the received
private literal at the correct host team. Network geometry supplies the owning
cell and the complete preceding bank width. -/
theorem joint_signedPointer_delivered
    (geo : RoutingOutputs.Image F (sid ∘ host) (portID ∘ live) x origin before)
    (image : (l).Image before dir.entries placed) (placedFit : (l).Fits w before)
    (delivery : ReturnedDelivery (wired) pin ext wire dir (pp) lp team arena stride H PL)
    (jointRoom : JointRoom dir start a boot geom) (teams : dir.teams=R+1)
    (tail : 0 < dir.literal/2) (short : dir.description ≤ dir.literal/2)
    (volume : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2))
    (j : Fin dir.entries) (bodyRoom : (Source.boxBody (fs j)).length ≤ cap)
    (tallyRoom : header+cap+(tally j).length ≤ dir.description)
    (address : opaquePointer (fun c => arena+c*stride) (fun c => before ((l).supplied+c))
      ((l).owner before) gap dir.description j < 2^w) :
    Source.Delivered (description := dir.description) (readings (H (team (cell (host j)).val)).history.val.2.2)
      (ParseBatchSort.value fun b => (SignedFields.frame F boxes entry arena stride gap dir.description g digits).eval
        x (.inr j,b)) header (fs j) := by
  have facts := geo.placed N cell (fun v => (state v).size) sid edgeID portID F physical codes sizeFit host live origin before
  have owns : (l).owner before j.val = (cell (host j)).val := by
    simpa only [RoutingOutputs.privateLayout,PrivatePlacement.Layout.owner,Packing.Directory.ISA.placement,
      Nat.mul_comm j.val 2] using congrArg Prod.fst (facts.1 j)
  rw [SignedFields.pointer_opaque F N cell (fun v => (state v).size) sid edgeID portID physical codes sizeFit
    boxes entry host hosts live frame origin arena stride gap dir.description before g digits geo placedFit j address]
  have sent := joint_opaquePointer_delivered P lib S dir pack boot geom bootBits geomBits header cap fs tally fit pin ext wire
    lp team arena stride H ib hb sb (l) before placed image placedFit rfl rfl delivery jointRoom teams tail short volume
    j bodyRoom tallyRoom
  rw [owns] at sent
  exact sent

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
