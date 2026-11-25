import OAI.Hierarchy.DescentTerminalPreflightMaskRoom
import OAI.Hierarchy.DescentTerminalPlacedSocketMask

namespace OAI
/-! # All measured primitive fields survive the intervening book and width programs -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentTerminalVertexFields DescentTerminalPrimitiveFrames DescentTerminalCompiledPrefix
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (start : ℕ) (V : Home.Format) (cfg : DescentTerminalCompiledPrefix.Shape)
  (I : Input) (head : ℕ) {vertices B w : ℕ} (short : vertices*span V.publicArity V.roles V.privateWords
    V.nodes V.addresses V.piece≤B) (literal : Literals I.sources)
local notation "floor_" => x.maskBase start
local notation "R_" => x.channels start
local notation "C_" => meter V R_ floor_
local notation "O_" => registers V cfg R_ floor_ head
local notation "base_" => afterMeter V cfg R_ floor_
local notation "A_" => rowArena cfg I base_
local notation "L_" => AddressPlan.layout cfg I base_ O_
local notation "socket_" => fun m : Memory w => Suffix.sockets cfg L_ ((A_).mount (input V cfg I R_ floor_ head short literal m))
local notation "reading" => measured (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
      (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (C_).layout

/-- The graph receipt for the immediate primitive output can be reused at the
true terminal date. Both runs use the same installed decoder and register layout. -/
theorem measured_after_preflight (primitive booked ports : Memory w)
    (before : ∀j<x.weights start,booked j=primitive j)
    (after_ : ∀j<x.weights start,ports j=booked j)
    (early : Earlier cfg I base_ (C_).layout w) (room : last V cfg I R_ floor_<2^w)
    {shops : ℕ} (i : Fin shops) : reading (socket_ ports) i=reading (socket_ primitive) i := by
  rw [sockets_measured V cfg I R_ floor_ head short literal ports early room (x.channels_before start),
      sockets_measured V cfg I R_ floor_ head short literal primitive early room (x.channels_before start)]
  funext f
  have at_ := bank_below primitive ports ((R_).bank f) (x.weights start) (x.channels_before_weights start f)
    (fun j hj=>(after_ j hj).trans (before j hj)) (i.val : Word w)
  simp only [measured,show (C_).layout.channel f=(R_).bank f from rfl,at_]

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
