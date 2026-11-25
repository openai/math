import OAI.Hierarchy.DescentVenueQuantityAny
import OAI.Hierarchy.DescentStageVenueTariff

namespace OAI
/-! # Native compilation costs of the reached-host remap for quantities and isolated actors -/
namespace Hierarchy.DescentVenueQuantityPlanes
open ProtocolRAM DescentSIMDLookup DescentActorRaster Computability.VPVNP.BurstRAM PrivateRAM
open DescentStaticWordColumn (names names_seq names_mount names_scan)
noncomputable section
def tableScanBill (cells rows op:ℕ):=
  (4+10*cells+(4+rows*(2*op+4)))+7*(15*(cells+1)+(11+4*op))
variable (p:Dims)
local notation "raw" => p.shapes*p.oldHosts
local notation "N" => p.oldHosts*p.shapes
local notation "rad" => p.groups*p.blocks
local notation "s" => chunks p.groups p.lanes
local notation "B" => p.blocks
local notation "w₀" => p.oldLanes
local notation "w₁" => p.lanes*p.blocks
local notation "a" => p.precision
def denseOp:=(DenseRead.expr 0 0 0 0 0 ⟨0,0⟩ ⟨0,0⟩ ⟨0,0⟩).work
def fee:=
  2048*((Overlap.pieces rad w₀ w₁+1)*(w₀+1)*2^(a*w₀)+Overlap.rows raw rad w₀+Overlap.rows raw rad w₁+1)+
  tableScanBill (DescentScalarBookReshape.cells p.oldHosts p.shapes p.groups B a p.lanes) (B*(N*s)) 25+
  tableScanBill (DenseRead.cells B p.hosts s 0 N) (B*(p.hosts*s)) denseOp

theorem billed (L:Layout)(w:ℕ)(old:0<w₀)(new:0<p.lanes)(blocks:0<B):
    (phase p L w).ticks+7*names (phase p L w).program≤fee p:=by
  have cost:=Overlap.tariff L.pitch raw rad w₀ w₁ a w L.earlier old (Nat.mul_pos new blocks)
  let converted:=Overlap.outputBank L.pitch raw rad w₀ w₁ a
  have reshape:(DescentScalarBookReshape.expression (DescentScalarBookReshape.layout p.oldHosts p.shapes
    p.groups B a p.lanes L.reshape converted)).work=25:=rfl
  dsimp only [converted] at reshape
  have dense:(DenseRead.expr B p.hosts s L.collect N L.count L.inverse L.grouped).work=denseOp:=rfl
  have cols:DenseRead.cells B p.hosts s L.collect N=DenseRead.cells B p.hosts s 0 N:=rfl
  simp only [phase,program,ticks,DescentScalarBookReshape.program,DenseRead.proc,names_seq,names_mount,
    names_scan,reshape,dense,cols,fee,tableScanBill]
  omega

end
end Hierarchy.DescentVenueQuantityPlanes

end OAI
