import OAI.Hierarchy.DescentRecordedRootSnapshot
import OAI.Hierarchy.DescentStageVenuePeers

namespace OAI
/-! # Previous host and neighbor words for the prepared reset roots -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentCompiler DescentSIMDLookup DescentPackedColony DescentGL DescentColonies
open DescentFallbackPeriod.Projected DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel
open DescentSharedCableNames.Stage DescentSharedBookScan DescentPlainTerminal DescentPlainTerminal.Suffix
open DescentRelativeContacts DescentGroupPeerOrder DescentStageEdgeReceipt DescentFallbackShapeTable DescentFallbackRankRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail H field : ℕ}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (pad : Fintype.card cap.V ≤ H)
set_option quotPrecheck false
set_option hygiene false
local notation "A" => cap.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "depth" => GroupStage.depthBound D n f g
local notation "host" => cap.vertex.trans (Fin.castLEEmb pad)
local notation "near_" => hostRoster A ((host).trans Fin.valEmbedding)
local notation "source_" => hostRotor host (hostRoster A (cap.vertex.trans Fin.valEmbedding))
local notation "sname" t => (shortName cc ((T).code t)).2
variable {w N K Rep M a b t : ℕ}
    (receiver : Receiver (A).degree (A).cap N (Z).n r cc H (S.groupCount i) K Rep M a b t field depth w)
    (book : RootBook (Z).n r (A).degree (2^r) (A).cap field)
    (old : Dated.Operands) {L countBits floor : ℕ} (first reached : Memory w)
    (source : stageVenue cap pad old L countBits floor (cap.venueRoster pad) first)
    (preserve : ∀addr,addr < floor → reached addr=first addr)

theorem root_neighbor (v : cap.V) (j : Fin (A).degree) :
    source_ (host v) j=(near_ v j).map host := by
  have found : ∃u,host u=host v:=⟨v,rfl⟩
  rw [hostRotor,dite_eq_left found,(host).injective found.choose_spec]
  rfl

include source preserve in
theorem root_old_words :
    (∀v (j : Fin (A).degree),reached (old.roster.base+((host v).val*(A).degree+j.val))=
      (hostDigit host (near_ v j):Word w)) ∧
    ∀v,reached (old.hubs.base+(host v).val)=(((A).hub v).toNat:Word w) := by
  have rfit : old.roster.Fits w floor:=source.1.roster
  have rsize : H*(A).degree ≤ old.roster.size:=by rw [cap.branch]; exact source.1.rosterRoom
  have hfit : old.hubs.Fits w floor:=source.2.2.2.2.1
  have hsize : H ≤ old.hubs.size:=source.2.2.2.2.2.1
  constructor
  · intro v j
    have offset : (host v).val*(A).degree+j.val < H*(A).degree := by
      simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (host v,j)).isLt
    rw [preserve _ ((Nat.add_lt_add_left (offset.trans_le rsize) _).trans_le rfit.2.2)]
    have saved:=cap.roster_read pad old source (host v) j
    rw [root_neighbor (cap:=cap) pad] at saved
    cases q₀ : near_ v j <;> simpa only [q₀,Option.map_none,Option.map_some,Option.elim_none,Option.elim_some,
      hostDigit,Nat.add_assoc] using saved
  · intro v
    rw [preserve _ ((Nat.add_lt_add_left ((host v).isLt.trans_le hsize) _).trans_le hfit.2.2)]
    have saved:=source.2.2.2.2.2.2.1 (host v)
    have real : ∃u,host u=host v:=⟨v,rfl⟩
    simp only [Census.hub,dite_eq_left real,(host).injective real.choose_spec] at saved
    cases hb : (A).hub v <;> simpa [hb] using saved

include source preserve in
/-- The root book reuses the original low host and adjacency banks throughout the
signed, stencil and rank passes. Its remaining inputs describe public sizes. -/
theorem venue_header (oldEnd : floor ≤ receiver.origin)
    (neighbors : book.previousNeighbors=old.roster) (hubs : book.previousHubs=old.hubs)
    (rate : book.fallbackDegree=32*Nat.clog 2 (2*(A).degree))
    (hbits : book.hubBits=g) (lbits : book.loadBits=f) (shapes : book.shapes=2^depth)
    (rowRoom : H < 2^w) (portRoom : (A).degree+1 < 2^w)
    (word : 0 < w) (tall : depth+2 ≤ w)
    (available : ∀v : (Z).Fallback,∀k x,x∈DescentFallbackLeafScan.localShape r (32*Nat.clog 2 (2*(A).degree))
      g f (sname v) k → shapeNumber x+1 < 2^w)
    (encoded : ∀v : (Z).Fallback,shapeNumber (sname v) < 2^w)
    (wires : DescentSignedCableCodec.width (A).degree (A).cap ≤ field) (ranks : depth+2 ≤ field) :
    OriginalHeader B pad receiver book reached := by
  obtain ⟨raw,flags⟩:=root_old_words (cap:=cap) pad old first reached source preserve
  have widen {bank : Bank} (fit : bank.Fits w floor) : bank.Fits w receiver.origin :=
    ⟨fit.1,fit.2.1,fit.2.2.trans oldEnd⟩
  refine ⟨rate,hbits,lbits,shapes,?_,?_,?_,?_,rowRoom,portRoom,?_,?_,word,tall,available,encoded,wires,ranks⟩
  · rw [neighbors]
    exact widen source.1.roster
  · simpa only [hubs] using widen source.2.2.2.2.1
  · rw [neighbors,cap.branch]; exact source.1.rosterRoom
  · simpa only [hubs] using source.2.2.2.2.2.1
  · simpa only [neighbors] using raw
  · simpa only [hubs] using flags

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
