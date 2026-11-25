import OAI.Hierarchy.DescentReachedOrdinaryRange
import OAI.Hierarchy.DescentPaidSweepTargetPadding
import OAI.Hierarchy.DescentOrdinaryRangeHostPadding
import OAI.Hierarchy.DescentRegisteredOperandReshape

namespace OAI
/-! The six components of each real seven-page W row on the original old population. -/
namespace Hierarchy.DescentLocalArchiveOrder.PaddedOrigin
open DescentNetworkPartition Computability.BorderVNP.Crossing
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i
local notation "NG" => S.groupCount (i+1)
local notation "span" => DescentHaloWalkRAM.breadth deg
local notation "ticketRows" => 1+(A).cap*6
local notation "roster" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
local notation "reach" => Gather.reaching roster
local notation "shelf" => 2^(packExponent 20 deg)+2
local notation "pitch" => (2^(k+1)-1)*shelf
local notation "raw" => 2^(k+1)*shelf

open DescentPaidResidentCount
variable {mb K₀ fieldBits : ℕ} (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
    (age : i<S.length) (radix : S.radix=2^k)
    (priorCount : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell mb)
    (previous : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (fieldBits*K₀))
    (born : Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell fieldBits)
local notation "oldN" => K₀
local notation "digits" => S.groupDigits age radix

open DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM
open DescentDatedPriorOperand DescentOperandStateBanks
variable {large roleBits args : ℕ} (wide : Fintype.card cap.V ≤ large)
local notation "up_" => Fin.castLEEmb wide
local notation "actual_" => Gather.reaching (hostRotor (cap.vertex.trans up_) (hostRoster A (cap.vertex.trans Fin.valEmbedding)))
local notation "oldGroup_" y:arg => (digits).symm (finProdFinEquiv.symm y)
variable (tall : Block k→Fin (1+cap.placement.cap*6)→Fin large→Fin (S.groupCount i)→Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
    (hubs : Fin large→Fin (S.groupCount i)→ Cell 1)
    (roles : Block k→Fin large→Fin (S.groupCount i)→Cell (roleBits*K₀))

/-- A single numerical W geometry shared by all seven original operand fields. -/
def acquiredGeometry (l : Fin pitch) :
    Values deg k K₀ (A).cap large (NG*2^k) fieldBits (Packed.bits pitch) mb :=
  { walks := actual_
    old := fun _ _ _=>0
    born := fun _ _ _ _ _=>0
    wanted := fun _ _=>Packed.token (some l)
    venues := fun h y=>DescentScalarVenueMask.fields actual_ tall hubs k (gainExponent 20 deg) shelf pitch h (oldGroup_ y)
    counts := fun h y=>DescentOrdinaryAtomFieldRAM.RoleCounts.value (K:=oldN) actual_ roles mb h (oldGroup_ y) }

variable (old : Pages args→Block k→Fin large→Fin (S.groupCount (i+1)*2^k)→Cell (fieldBits*K₀))
    (fresh : Pages args→Block k→Fin cap.placement.cap→Fin 6→Fin large→Fin (S.groupCount (i+1)*2^k)→Cell fieldBits)

/-- The stamped per-page W value agrees on the authentic compact host, including
the full prior node count and the placement of all old/fresh fields. -/
theorem acquired_prefix (pg : Pages args) (l : Fin pitch)
    (liveRows : ∀b s h g,tall b s (up_ h) g=tokens b s h g)
    (liveHubs : ∀h g,hubs (up_ h) g=flags (cap:=cap) h g)
    (priorRoles : ∀b h g,DescentOrdinaryAtomFieldRAM.RoleCounts.count (a:=roleBits) (K:=oldN) mb (roles b (up_ h) g)=priorCount b h g)
    (oldCells : ∀b h y,old pg b (up_ h) y=previous b h (oldGroup_ y))
    (birthCells : ∀b s j h y,fresh pg b s j (up_ h) y=born b s j h (oldGroup_ y)) :
    Values.Prefix wide
      (rangeValues ticket arch tokens age radix priorCount previous born l)
      (OrdinaryBooks.inputs old fresh
        (acquiredGeometry (fieldBits:=fieldBits) (mb:=mb) (K₀:=K₀) (cap:=cap) age radix wide tall hubs roles) pg l) := by
  have sameRows (h : Fin OH) (s : Fin span) : actual_ (up_ h) s=(reach h s).map up_ :=
    reaching_pad wide roster _ (physical_rotor wide cap.vertex _) h s
  refine ⟨sameRows,oldCells,birthCells,fun _ _=>rfl,?_,?_⟩
  · intro h y
    funext j
    exact fields_real wide reach actual_ sameRows tokens tall (flags (cap:=cap)) hubs k (gainExponent 20 deg)
      shelf pitch liveRows liveHubs h (oldGroup_ y) j
  · intro h y
    funext j
    let p : Fin span × Fin (2^k) := finProdFinEquiv.symm j
    change (DescentSortedRoster.indexed actual_ (up_ h) p.1).elim 0 _ =
      (DescentSortedRoster.indexed reach h p.1).elim 0 _
    rw [DescentSortedRoster.indexed_pad wide reach actual_ h (sameRows h) p.1]
    cases atDonor : DescentSortedRoster.indexed reach h p.1 with
    | none => rfl
    | some u => exact priorRoles p.2 u (oldGroup_ y)

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
