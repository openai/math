import OAI.Hierarchy.DescentOrdinaryRangeAcquisition
import OAI.Hierarchy.DescentVacantOrdinaryPayload

namespace OAI
/-! Occupied and ghost W stamps from the registered ordinary geometry. -/
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
local notation "N₀" => DescentPackedActorMask.nodes (span*2^k) oldN (A).cap
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

open DescentOrdinaryRasterReturn
local notation "geom" => acquiredGeometry (fieldBits:=fieldBits) (mb:=mb) (K₀:=K₀) (cap:=cap) age radix wide tall hubs roles
/-- The original W input from a reached board emits the same one-based origin stamp on the
entire wide host rectangle, including inactive hosts and all missing/empty source slots. -/
theorem acquired_stamp {K' b:ℕ} (l:Fin pitch) (h:Fin large) (y:Fin (NG*2^k))
    (actual:∀x s h g,tall x s (up_ h) g=tokens x s h g)
    (unused:∀x s (h:Fin large) g,OH≤h.val→tall x s h g=none)
    (hub:∀h g,hubs (up_ h) g=flags (cap:=cap) h g)
    (population:∀x h g,DescentOrdinaryAtomFieldRAM.RoleCounts.count (a:=roleBits) (K:=oldN) mb
      (roles x (up_ h) g)=priorCount x h g):
    DescentOrdinaryOriginMask.selection N₀ K' b (DescentOrdinaryOriginMask.marked (geom l) h y)=
      DescentOrdinaryRasterReturn.extend (H:=large) (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l) h y:=by
  by_cases live:h.val<OH
  · let u:Fin OH:=⟨h.val,live⟩
    have place : up_ u=h:=Fin.ext rfl
    have prior_:=acquired_prefix (args:=1) ticket arch tokens age radix priorCount
      (fun _ _ _=>(0:Cell (fieldBits*oldN))) (fun _ _ _ _ _=>(0:Cell fieldBits)) wide tall hubs roles
      (fun _ _ _ _=>0) (fun _ _ _ _ _ _=>0) 0 l actual hub population (fun _ _ _=>rfl) (fun _ _ _ _ _=>rfl)
    have venue:=prior_.venues u y
    have counts:=prior_.counts u y
    simp only [DescentOrdinaryOriginMask.marked]
    change DescentOrdinaryOriginMask.selection _ _ _ (DescentPackedActorMask.occupied _ _ _ _
      (DescentPackedActorMask.target _ _ (Packed.token (some l)) (encode _ _ ((geom l).venues h y)))
      (encode _ _ ((geom l).counts h y)))=_
    have atHost : DescentOrdinaryRasterReturn.extend (H:=large) (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l) h y=
        oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l u y:=dite_eq_left live
    change (geom l).venues (up_ u) y = _ at venue
    change (geom l).counts (up_ u) y = _ at counts
    rw [atHost,←place,venue,counts]
    rfl
  · rw [show DescentOrdinaryRasterReturn.extend (H:=large) (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l) h y=0
      from dite_eq_right live]
    apply DescentOrdinaryOriginMask.vacant
    intro j equal
    have missing:=fields_ghost (H:=OH) (large:=actual_) (t':=tall) (hubs':=hubs) k (gainExponent 20 deg)
      shelf pitch h (oldGroup_ y) j (padded_donor_blank wide cap.vertex _ h (Nat.le_of_not_gt live))
      (fun x s u hu=>unused x s u _ hu)
    change DescentScalarVenueMask.fields actual_ tall hubs k (gainExponent 20 deg) shelf pitch h (oldGroup_ y) j=Packed.token (some l) at equal
    rw [missing] at equal
    have bad:=congrArg Fin.val equal
    change 0=l.val+1 at bad
    omega

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
