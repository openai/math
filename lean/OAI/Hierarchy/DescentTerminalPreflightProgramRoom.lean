import OAI.Hierarchy.DescentTerminalPreflightInvoice
import OAI.Hierarchy.DescentTerminalPreflightCalibration
import OAI.Hierarchy.DescentTerminalPreflightBook

namespace OAI
/-! # Paying the actual preflight program from the selected room for its numeric registers -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentTerminalGrainProfiles DescentTerminalLocalPortBook DescentTerminalPrimitiveArena
open DescentSIMDLookup DescentTerminalPointerDigits ProtocolRAM DescentTerminalHeaderDraft DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable (x:DescentTerminalPreflightSpace.Spec) (origin:ℕ) (peer:Bank)
    (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
local notation "H0" => x.scalar.shops
local notation "B0" => x.scalar.blocks
local notation "bk" => x.issuedBook origin peer old
local notation "tape" => x.cables origin peer old
local notation "ctr" => x.controls origin
local notation "pub" => x.publicWidths origin
local notation "actorStart" => DescentTerminalPriorArena.actStart x.scalar x.groups x.paidLanes x.paidBits x.externalBits (x.cohortEnd origin)

/-- Every hypothesis of the instruction invoice involving a parameter is a
projection of this record. The earlier calibration implies it on real charts. -/
structure ProgramRoom (h factor paid:ℕ) : Prop where
  books : DescentTerminalPointerFrame.size x.strips x.printBits≤2^(h/2)
  cables : (tape).fee≤2^(h/2)
  counts : (tape).printer.entries≤4*2^(h/2)
  bookRows : ((bk).homes+1)*(x.strips+1)≤H0*(4*factor)
  cableRows : ((tape).tickets+1)*((tape).cols+1)≤H0*(4*factor)
  scalarRows : (H0+1)*(x.scalar.columns+1)*(B0+1)≤H0*(4*factor)
  pointer : DescentTerminalPointerFrame.size x.scalar.columns x.scalar.pointerBits≤2^(h/2)
  counter : DescentTerminalPointerFrame.size 3 x.scalar.countBits≤2^(h/2)
  weights : Book.WeightShelf.words x.vertices x.arguments≤6*2^(h/2)
  data : (ctr).codeWords≤2^(h/2)
  shift : (ctr).shape.limit≤2^(h/2)
  addresses : (ctr).sites≤H0*(4*factor)
  tapeCap : (tape).maxRows≤paid
  widthAndDraft : (pub).rows+x.paidRows≤paid
  priorPacking : B0*(1+(chunks x.groups x.paidLanes+chunks x.groups x.actorLanes))≤4*factor
  menus : DescentTerminalPopulation.RAM.lease H0 x.groups x.paidLanes x.paidBits x.externalBits (x.cohortEnd origin)+
      DescentTerminalActorRepack.count H0 x.groups x.actorLanes 1 B0 actorStart+
      (DescentTerminalPublicCountRAM.lut (pub).base (pub).maxCohorts).size+(pub).widthLayout.entries≤
      12*(2^(h/2)+H0*(4*factor))

theorem program_room {h factor paid:ℕ} (s:x.ScalarRoom h factor paid)
    (Hpos:0<H0) (Bpos:0<B0) (Dpos:0<x.degree) (gp:0<x.groups) (publicPos:0<x.publicGrains)
    (a:x.groups≤x.actorLanes) (p:x.groups≤x.paidLanes) :
    ProgramRoom x origin peer old h factor paid := by
  let U:=2^(h/2)
  have positive:=s.scale_pos
  have rate:0<4*factor:=by omega
  have strip:=s.stripCount
  have cable:=s.cableCount
  have prim:=s.primitive
  have numeric (L d:ℕ) (l:0<L) (bits:d*L+Nat.clog 2 (L+1)≤h/2) :
      DescentTerminalPointerFrame.size L d≤2^(h/2):=fee_le L d (h/2) l bits
  have scalarScan:(H0+1)*(x.scalar.columns+1)*(B0+1)≤H0*(4*factor):=by
    have a:=Nat.mul_le_mul_left H0 prim
    have hb:B0≤H0*B0:=Nat.le_mul_of_pos_left _ Hpos
    have hs:x.scalar.columns≤x.scalar.columns*B0:=Nat.le_mul_of_pos_right _ Bpos
    have hh:x.scalar.columns*B0≤H0*(x.scalar.columns*B0):=Nat.le_mul_of_pos_left _ Hpos
    have bh:H0≤H0*B0:=Nat.le_mul_of_pos_right _ Bpos
    have ll:H0*x.scalar.columns≤H0*(x.scalar.columns*B0):=Nat.mul_le_mul_left _ hs
    ring_nf at a hb hs hh bh ll ⊢
    omega
  have cableScan:((tape).tickets+1)*((tape).cols+1)≤H0*(4*factor):=by
    change (H0*x.degree+1)*(x.widthColumns+1)≤_
    have a:=Nat.mul_le_mul_left H0 cable
    have hd:=Nat.le_mul_of_pos_right H0 Dpos
    have hm:=Nat.le_mul_of_pos_left (x.widthColumns+1) (Nat.mul_pos Hpos Dpos)
    ring_nf at a hd hm ⊢
    omega
  have bookScan:((bk).homes+1)*(x.strips+1)≤H0*(4*factor):=by
    change (H0+1)*(x.strips+1)≤_
    have a:=Nat.mul_le_mul_left H0 strip
    have b:=Nat.le_mul_of_pos_left x.strips Hpos
    have ht:=Nat.le_mul_of_pos_right H0 positive
    ring_nf at a b ht ⊢
    omega
  have rounded : 2^Nat.clog 2 (x.cableCap+1)≤2^(h/2):=Nat.pow_le_pow_right (by decide)
    ((Nat.clog_le_iff_le_pow (by decide)).2 s.cablePopulation)
  have cap:(tape).printer.entries≤4*2^(h/2):=by
    change 2*(2^Nat.clog 2 (x.cableCap+1))≤_
    omega
  have pc:(pub).maxCohorts+1≤2^(h/2):=by
    change 2^x.cohortBits+1≤_
    have z:=Nat.le_mul_of_pos_right (2^x.cohortBits) publicPos
    exact (Nat.add_le_add_right z 1).trans s.publicPopulation
  have count:DescentTerminalPointerFrame.size 3 x.scalar.countBits≤2^(h/2):=by
    apply numeric 3 x.scalar.countBits (by decide)
    simpa only [show Nat.clog 2 (3+1)=2 by decide,Nat.mul_comm] using s.countShape
  refine ⟨numeric _ _ s.bookColumns s.bookShape,numeric _ _ (show 0<x.widthColumns by change 0<1+_;omega) s.cableShape,
    cap,bookScan,cableScan,scalarScan,numeric _ _ s.pointerCols s.pointerShape,count,s.weights,s.book,s.shift,
    ?_,s.rows.trans' (Nat.le_add_left x.headerRows x.paidRows),
    (Nat.add_comm x.headerRows x.paidRows).le.trans s.rows,
    packed_lanes (gp.trans_le p) (gp.trans_le a) p a (by
      have small:=Nat.mul_le_mul_right B0 (show 3≤x.scalar.columns+16 by omega)
      omega),?_⟩
  · change H0≤H0*(4*factor);exact Nat.le_mul_of_pos_right _ rate
  · simpa only [Nat.add_assoc] using menu_price H0 x.groups x.paidLanes x.paidBits x.externalBits (x.cohortEnd origin) x.actorLanes actorStart
      (pub) h (4*factor) rate s.actorChunks s.paidChunks s.paidWidth (by simpa using s.actorWidth)
      s.exteriorWidth pc s.publicPopulation

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
