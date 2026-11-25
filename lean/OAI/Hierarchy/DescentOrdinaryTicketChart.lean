import OAI.Hierarchy.DescentNamedOrdinaryVenue
import OAI.Hierarchy.DescentDatedDonorOutputs
import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentPackedEpochBill
import OAI.Hierarchy.DescentNamedMeterCode

namespace OAI
/-! # Public parameters for turning a selected ordinary edge into a native date -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local DescentOperandVectorArena
open DescentSIMDLookup ProtocolRAM
noncomputable section

/-- The finite operand and node layouts supplied by the preceding date and by
the global public table dimensions. These layouts carry no selected ticket. -/
structure OrdinaryBooks where
  reference : DescentOrdinaryRefsROM.Chart
  bornBook : DescentOrdinaryBorn.Chart
  ingressWords : ℕ
  vector : Layout
  resolver : DescentDatedPriorOperand.Layout
  origin : DescentDatedPriorOperand.OriginPlan resolver
  palette : DescentOrdinaryPalette.Configuration
  metadata : MetadataReturn
  operandBook : DescentOrdinaryFinal.Chart

namespace OrdinaryBooks
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k age z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {src : Reached W G q ε S k age z D wire hist} {he : 0≤ ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {dst : Reached n.result G q ε S k (age+1) z' D' wire hist}
    (e : OrdinaryBooks) (ticket : OrdinaryLink src he T c n dst)
    (gain tail p f payload seats hostLanes : ℕ) (old : Bank)
    (ordinary : ℕ→Stage.Dated.Ordinary)

local notation "date" => DonorDate.atDate G S gain k age p
local notation "hostLevel" => Nat.clog 2 (S.hostSize age)
local notation "b" => S.censusBits p
local notation "field" => DescentTerminalEpochBits.width G.C
set_option quotPrecheck false in
local notation "area" => (date).schedule payload seats b

/-- Ticket-independent packing, original profile pitch, matcher shape, signed
successor and normalized venue, with the actual reached states as witnesses. -/
def onTicket : PhysicalOrdinary F P where
  dimension:=d
  bits:=bits
  gadget:=G
  schedule:=S
  q:=q
  u:=u
  ε:=ε
  k:=k
  age:=age
  z:=z
  degree:=D
  wire:=wire
  hist:=hist
  nextZ:=z'
  nextDegree:=D'
  world:=W
  prior:=src
  nonnegative:=he
  stage:=T
  choice:=c
  normalize:=n
  target:=dst
  ticket:=ticket
  old:=old
  rasterLanes:=hostLanes*(2^k)
  signed:=SignedStage.signedAt G S gain k age payload
  venue:=StageVenueTail.Date.atOrdinary G S gain k tail p f payload ordinary age hostLanes
  level:=hostLevel
  bitsPerField:=b
  short:=max (k+3) (Nat.clog 2 ((area).D+1))
  payload:=payload
  unit:=(date).amount
  profile:=field
  seats:=seats
  profileRepack:=⟨seats,DescentPackedEpochShelves.grain (payload/2) G.C,(area).lanesAt*(area).shapeAt.pairs,field⟩
  reference:=e.reference
  bornBook:=e.bornBook
  ingressWords:=e.ingressWords
  vector:=e.vector
  resolver:=e.resolver
  origin:=e.origin
  palette:=e.palette
  metadata:=e.metadata
  operandBook:=e.operandBook

end OrdinaryBooks
end
end Hierarchy.DescentSixParty.Chronology

end OAI
