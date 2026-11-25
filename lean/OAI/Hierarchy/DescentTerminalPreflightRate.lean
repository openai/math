import OAI.Hierarchy.DescentTerminalPreflightLengths

namespace OAI
/-! # Bounding true RAM high-water from the purchased site count and finite alphabets -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentTerminalPrimitiveArena DescentTerminalLocalPortBook DescentTerminalGrainProfiles
open ProtocolRAM DescentSIMDLookup
noncomputable section
variable (x:Spec) (h scale paid:ℕ)
local notation "H" => x.scalar.shops
local notation "B" => x.scalar.blocks
local notation "U" => 2^(h/2)
local notation "R" => H*scale
/-- Original scalar, cable, page and fixed-book sizes. The bound on the numbers of
occupied groups is independent of the machine word width or the initial RAM address. -/
structure ScalarRoom : Prop where
  scale_pos : 0<scale
  incoming : x.frozenBits+x.cohortBits≤h/2
  paidWidth : x.paidBits*x.paidLanes≤h/4
  actorWidth : x.actorLanes≤h/4
  exteriorWidth : x.externalBits≤h/2
  paidChunks : chunks x.groups x.paidLanes≤2^(h/4)
  actorChunks : B*chunks x.groups x.actorLanes≤2^(h/4)
  pointerCols : 0<x.scalar.columns
  pointerShape : x.scalar.pointerBits*x.scalar.columns+Nat.clog 2 (x.scalar.columns+1)≤h/2
  countShape : 3*x.scalar.countBits+2≤h/2
  bookColumns : 0<x.strips
  bookShape : x.printBits*x.strips+Nat.clog 2 (x.strips+1)≤h/2
  cableShape : x.cableCellBits*x.widthColumns+Nat.clog 2 (x.widthColumns+1)≤h/2
  weights : Book.WeightShelf.words x.vertices x.arguments≤6*U
  book : x.controlBytes≤U
  shift : x.controlShape.limit≤U
  cablePopulation : x.cableCap+1≤U
  publicPopulation : 2^x.cohortBits*x.publicGrains+1≤U
  primitive : (x.scalar.columns+16)*B≤ scale
  stripCount : x.strips≤ scale
  cableCount : (x.widthColumns+1)*x.degree≤ scale
  cohorts : x.cohorts≤R+paid
  rows : x.paidRows+x.headerRows≤paid

theorem extent_rate (base:ℕ) (s:x.ScalarRoom h scale paid) :
    x.maskBase base≤base+512*(U+R+paid+1) := by
  have low:=s.scale_pos
  have host:H≤R:=Nat.le_mul_of_pos_right H low
  have pop:=s.cohorts
  have live:=s.rows
  have floor_:0<U:=Nat.two_pow_pos _
  have pow_ (j k:ℕ) (e:j≤k) : 2^j≤2^k:=Nat.pow_le_pow_right (by decide) e
  have fcap:=s.incoming
  have fr:=pow_ x.frozenBits (h/2) (by omega)
  have cb:=pow_ x.cohortBits (h/2) (by omega)
  have key:2^x.cohortBits*2^x.frozenBits≤U:=by rw [←pow_add,Nat.add_comm];exact pow_ _ _ fcap
  have inc:x.incomingWords≤8*U+24*(R+paid+1) := by
    change 2^x.frozenBits+2^x.cohortBits+(2^x.cohortBits*2^x.frozenBits)+3*pad x.cohorts+2*pad H+4*x.cohorts+2*H+2≤_
    have:=pad_le x.cohorts;have:=pad_le H;omega
  have sq:2^(h/4)*2^(h/4)≤U:=by rw [←pow_add];exact pow_ _ _ (by omega)
  have pa:=(Nat.mul_le_mul s.paidChunks (pow_ _ _ s.paidWidth)).trans sq
  have ac:=(Nat.mul_le_mul s.actorChunks (pow_ _ _ s.actorWidth)).trans sq
  have roles:=pow_ _ _ s.exteriorWidth
  have menus:x.oldMenus≤3*U:= by unfold oldMenus;omega
  have hN:=Nat.mul_le_mul_right H s.primitive
  have vol:(x.scalar.columns+16)*x.scalar.rows≤R:=by
    simpa [DescentTerminalPrimitiveArena.Shape.rows,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using hN
  have rle:x.scalar.rows≤R := (Nat.le_mul_of_pos_left _ (by omega : 0<x.scalar.columns+16)).trans vol
  have prior:x.oldWords≤4*U+16*(R+1) := by
    unfold oldWords DescentTerminalPrimitiveArena.Shape.guard
    have:=pad_le H;have:=pad_le x.scalar.rows;omega
  have pf:=fee_le _ _ _ s.pointerCols s.pointerShape
  have depth:Nat.clog 2 (3+1)=2:=by decide
  have nf:=fee_le 3 x.scalar.countBits (h/2) (by decide) (by rw [depth];simpa only [Nat.mul_comm 3] using s.countShape)
  have prim:x.primitiveWords≤3*U+20*(R+1):=by
    unfold primitiveWords
    have extra:(x.scalar.columns+6)*x.scalar.rows≤R :=
      (Nat.mul_le_mul_right _ (show x.scalar.columns+6≤x.scalar.columns+16 by omega)).trans vol
    have:=pad_le x.scalar.rows;have:=pad_le H;omega
  have groups:=s.bookColumns
  have bf:=fee_le _ _ _ groups s.bookShape
  have got:=s.weights
  have sh:=Nat.mul_le_mul_right H s.stripCount
  have bk:x.bookWords≤12*U+40*(R+1):=by
    unfold bookWords;have:=pad_le H;rw [Nat.mul_comm scale H] at sh;omega
  have cbound:=pad_le x.controlBytes
  have shift:=pad_le x.controlShape.limit
  have cbits:=s.book;have srooms:=s.shift
  have ctrl:x.controlWords≤10*U+10*(R+1):=by
    unfold controlWords
    have:=pad_le x.controlBytes;have:=pad_le x.controlShape.limit;have:=pad_le H;omega
  have cols:0<x.widthColumns:=by change 0<1+_;omega
  have cf:=fee_le _ _ _ cols s.cableShape
  have loc:=Nat.mul_le_mul_left H s.cableCount
  have both:x.widthColumns*x.tickets+x.tickets≤R:=by
    simpa [tickets,Nat.add_mul,Nat.mul_add,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using loc
  have cap:=s.cablePopulation
  have cab:x.cableWords≤6*U+24*(R+paid+1):=by
    unfold cableWords
    have:=pad_le x.tickets;have:=pad_le (x.cableCap+1);have:=pad_le x.headerRows;omega
  have pp:=s.publicPopulation
  have pub:x.publicWords≤8*U+12*(R+paid+1):=by
    unfold publicWords
    have:=pad_le (2^x.cohortBits+1);have:=pad_le (2^x.cohortBits*x.publicGrains+1)
    have:=pad_le H;have:=pad_le x.headerRows;omega
  have ev:x.eventWords≤180*(R+paid+1):=by
    unfold eventWords
    have:=DescentTerminalHeaderDraft.span_price x.paidRows
    have:=ProtocolRAMPurchaseSampler.span_le (2*H+x.paidRows+0+1)
    have:=pad_le x.paidRows;omega
  rw [section_end]
  unfold words
  omega

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
