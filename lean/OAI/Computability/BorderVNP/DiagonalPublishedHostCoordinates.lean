import OAI.Computability.BorderVNP.DiagonalPublishedSlottedReadback

/-! # Identifying the registered pin state across equal native layouts -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Packing PackedHistoryCircuit TeamContraction JointHeader ProcessorSlots
open VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator TeamSite
open CellMacro.Generator

/-- Transfer the original geometry header to the same physical memory in an equal layout. -/
theorem headerAtRegisteredMemory {w frame origin entries : ℕ} {ar br : SignedTaskArena.Layout}
    {mem seen : Memory w}
    (header : RoutingOutputs.Header frame origin ar.cube.cables ar.cube.cells entries (readings mem))
    (same : ar=br) (memory : seen=mem) :
    RoutingOutputs.Header frame origin br.cube.cables br.cube.cells entries (readings seen) := by
  cases same
  exact memory ▸ header

/-- The pin publication belongs to the same returned registers, memory and charged profile. -/
theorem pinAtRegisteredState {D p w d g : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {task : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits}
    {cell : N.Site → Fin task.cube.cells} {edge : N.Edge ↪ Fin task.cube.cables} {port : P ↪ Fin p}
    {original : Fin dir.entries → N.Site} {live : (Fin dir.teams × Fin dir.sites) ↪ P}
    {a : StartupArena} {u : Fin a.teams} {slot : ℕ} {packet : ReferencePacket w d} {origin gap : ℕ}
    {f : BroadcastFrame} {hdr : List Bool} {fields : Pins.ProcessorFields (a.operands u slot packet).layout}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {v : Fin g → Bool}
    {postPin regs rr : Bank w} {pinMem mem seen : Memory w} {used cost consumed charged : ℕ} {br : SignedTaskArena.Layout}
    (pin : PublishedPin task dir N cell edge port original live a u slot packet origin gap f hdr fields pub mac v
      postPin pinMem regs mem used cost)
    (same : task=br) (hr : rr=regs) (hm : seen=mem) (hp : consumed=used) (hc : charged=cost) :
    PublishedPin br dir N
      (cast (congrArg (fun ar : CubeArena.Layout => N.Site → Fin ar.cells) (congrArg SignedTaskArena.Layout.cube same)) cell)
      (cast (congrArg (fun ar : CubeArena.Layout => N.Edge ↪ Fin ar.cables) (congrArg SignedTaskArena.Layout.cube same)) edge)
      port original live a u slot packet origin gap f hdr fields pub mac v postPin pinMem rr seen consumed charged := by
  cases same
  exact hr ▸ hm ▸ hp ▸ hc ▸ pin

open Packing.RoutingOutputs RoutingISA.SignedTaskArena GeometryFrameEncoding
open VPVNP.VerifierNetwork

/-- The original placement passes certify both capacity and the actual memory at its return. -/
theorem publishedHostPlacement {D p w d g : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {task : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits}
    {cell : N.Site → Fin task.cube.cells} {edge : N.Edge ↪ Fin task.cube.cables} {port : P ↪ Fin p}
    {original : Fin dir.entries → N.Site} {live : (Fin dir.teams × Fin dir.sites) ↪ P}
    {a : StartupArena} {u : Fin a.teams} {slot : ℕ} {packet : ReferencePacket w d} {origin gap : ℕ}
    {f : BroadcastFrame} {hdr : List Bool} {fields : Pins.ProcessorFields (a.operands u slot packet).layout}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {v : Fin g → Bool}
    {postPin regs : Bank w} {pinMem mem seen middle : Memory w} {used cost : ℕ} {br : SignedTaskArena.Layout}
    (pin : PublishedPin task dir N cell edge port original live a u slot packet origin gap f hdr fields pub mac v
      postPin pinMem regs mem used cost)
    (layout : task=br) (epoch : Returns epochPlacement pub mac postPin pinMem)
    (publication : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
    (geometry : seen=mem) (middleEq : epoch.val.2.2=middle) :
    (privateLayout a.frame origin br.cube.cables br.cube.cells dir.entries dir.description gap).Fits w (readings seen) ∧
    (privateLayout a.frame origin br.cube.cables br.cube.cells dir.entries dir.description gap).Image
      (readings seen) dir.entries (readings middle) := by
  cases layout
  rw [geometry,←middleEq]
  have run := PublishedPin.actual_slotted task dir N cell edge port original live a u slot packet origin gap f hdr
    fields pub mac v postPin pinMem regs mem used cost pin epoch publication
  exact ⟨run.2.1,run.2.2.1⟩

end Diagonal

end BorderVNP
end Computability
end OAI
