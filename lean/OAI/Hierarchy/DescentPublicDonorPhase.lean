import OAI.Hierarchy.DescentTerminalEpochBits
import OAI.Hierarchy.DescentDonorPublicBanks
import OAI.Hierarchy.DescentPrivateDonorAllocation
import OAI.Hierarchy.DescentPrivateGatherPhase

namespace OAI
/-! # Fixed native donor installation, geometry lookup and six-source gather at a public date -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentRawCablePanel DescentPacking.PackedMatch.Local DescentHostDegree DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false

/-- The two rank encodings agree on actual placements. Keeping their numeric inputs
separate here makes the lowering from the typed receipt compute by reflexivity. -/
structure DonorDate where
  exponent : ℕ
  degree : ℕ
  cap : ℕ
  rankExponent : ℕ
  rankDegree : ℕ
  grain : ℕ
  hosts : ℕ
  groups : ℕ
  branch : ℕ
  colors : ℕ
  padding : ℕ

namespace DonorDate
variable (d : DonorDate)

def format : DepotRAM.Shape :=
  ⟨2^d.exponent,d.degree,d.cap,max (d.exponent+3) (Nat.clog 2 (d.degree+1)),
    donorNameBits d.rankExponent d.rankDegree,normBits d.cap d.branch d.colors d.padding⟩

def matcher := shape (2^d.exponent) d.degree (2*d.cap) (DescentTerminalEpochBits.width d.colors)

def amount :=
  let f:=d.format
  let full:=max (bundleBits 3 f.names f.widths) ((2+f.widths)*11)
  max (max (DepotRAM.totalBits f) ((2^d.exponent*d.cap)*full))
    (max (DepotRAM.Fresh.laneWidth f d.matcher) (2*DepotRAM.totalBits f+1))

variable (payload base : ℕ)
local notation "f" => d.format
local notation "s" => d.matcher
local notation "r" => 2^d.exponent
local notation "K₀" => 2^(d.exponent+1)
local notation "H" => d.hosts
local notation "J" => d.groups
local notation "M" => lanes payload d.amount
local notation "rows" => H*chunks J M
local notation "size" => DepotRAM.Setup.words f s K₀ H J M d.amount
local notation "rootAt" => DonorSpace.dynamicStart base size
local notation "span₀" => DepotRAM.Resident.Dynamic.Placement.endAddress H J M d.degree (DepotRAM.rawBits f) 0
local notation "src" => DonorSpace.source base size span₀ rows
local notation "end₀" => DonorSpace.meterBase base size span₀ rows
local notation "second" => base+DescentSIMDLookup.Book.words (DepotRAM.totalBits f) H J M
local notation "leaf" => second+DepotRAM.Binary.count f*(2*2^(d.amount*M))

def meterBase := end₀

def endAddress := DonorSpace.endAddress base size span₀ rows payload

def phase (bw : ℕ) (old : OrdinaryLink.PriorBanks r d.degree d.cap K₀) : NativePhase bw :=
  let address:=OrdinaryLink.publicAddressed f s K₀ H J M d.amount rootAt second leaf old
  let common:=DepotRAM.Resident.addressed f address H
  let sourceFields:=DepotRAM.Resident.fields f s common H J M
  let setup:=DepotRAM.Setup.phase f s K₀ H J M d.amount base d.cap (DescentTerminalEpochBits.width d.colors)
    d.colors d.padding d.grain d.branch (2^(packExponent 20 d.rankDegree)+2) bw
  let venues:=DepotRAM.Resident.Dynamic.Placement.issuedPhase H J M d.degree r (2*d.cap)
    (f).short d.cap (DescentTerminalEpochBits.width d.colors) bw rootAt old.peers.roster old.hub common.terrain
  let gathered:=DepotRAM.phase (DepotRAM.Binary.joints f M d.amount second) sourceFields
    (DescentSIMDLookup.Book.banks base (DepotRAM.totalBits f) H J M src) (end₀+1) H J M bw
  (setup.seq venues).seq gathered

def fromPrior (bw : ℕ) (prior : OrdinaryLink.PriorSource) := d.phase payload base bw (prior r d.degree d.cap K₀)

end DonorDate
end
end Hierarchy.DescentSixParty.Chronology

end OAI
