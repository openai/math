import OAI.Hierarchy.DescentMeasuredPublicBoard
import OAI.Hierarchy.DescentIssuedMatrixPacket
import OAI.Hierarchy.DescentMeasuredSenderDesk

namespace OAI
/-! # The board supplied to an actual recorded public socket -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentResetHostSize DescentSIMDLookup DescentSharedBookScan
open DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected DescentGroupPeerOrder
open DescentPaidResidentCount.Reset DescentOldContactSender DescentStageEdgeReceipt DescentRosterOrder
open DescentSharedCableNames.Stage DescentIssuedFallbackPanel DescentResetLocalRoster DescentPacking
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail field : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "c" => (T).commonDepth
local notation "r" => (Z).k-c
local notation "population" => 2^(Z).n
local notation "H" => S.hostSize i
local notation "dep" => GroupStage.depthBound D n f g
local notation "host" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "dim" => S.groupWidth k tail i+k
local notation "L" => 2^(dim-c)
local notation "short" => B.frame.enough.trans (Nat.sub_le ..)
local notation "name" => Recorded.oldName input
local notation "next" => PackedFlow.Padded.roster (D:=(A).degree) (A) name input.valid.host
local notation "paid" => Recorded.paddedValue (b:=field) c r next (Recorded.oldDepth B) (Recorded.oldWidth B)
variable (snap : PaddedSnapshot B input.valid.host field)
local notation "rank" => ranks (a:=r) (Y:=population) (D:=(A).degree) snap.chart (2^dep) (dep+2) snap.memory


local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (groupRank (Fin.valEmbedding (n:=S.groupCount i)) ((host).trans Fin.valEmbedding))
local notation "here" => donor (S.resetInputDigits ctl.base ctl.radix i) B.frame.basis short
local notation "native" => B.order.trans Fin.valEmbedding

/-- Express the public socket's mathematical board at the actual reached
width, grain count and terminal roster. -/
def recordedBoard (v : input.V) (hi : Block c) : RowData (A).degree L (A).cap field := by
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
  rcases B with ⟨ct,rfl,fit₀,order,eq_,Z₀,T₀,age,date,extent,tickets,unit,dimension,tape,board,
    frame,listed,raw,geometry,hubs,valid,grain,wire,atoms,branch,capacity⟩
  subst order
  let digits:=S.resetInputDigits ctl.base ctl.radix i
  let groups:=Fin.valEmbedding (n:=S.groupCount i)
  let large:=compact.trans (Fin.castLEEmb ready.host)
  exact GroupStage.boardFor phase S ready digits oldOrder Z₀ T₀ frame groups large snap.word
    (ranks snap.chart (2^(GroupStage.depthBound D n f g)) (GroupStage.depthBound D n f g+2) snap.memory) v hi

/-- The public column read issued by the preceding native packet stage agrees
at every ordinal, including every padding entry, with the measured socket board. -/
theorem recorded_padded_board
    (stencil : Fin H→Block c→Fin L→ℕ)
    (marks : Fin H→Block c→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap))
    (own : ∀v hi j,stencil (host v) hi j=snap.word (here v hi j))
    (marked : ∀v hi j l,marks (host v) hi j l=
      signedPanel (A) native S input.valid names (here v hi j) l)
    (v : input.V) (hi : Block c) (j : DescentRotorWindowArchive.Input (A).degree L (A).cap) :
    RootSources.paddedRow stencil next marks (fun u j=>((rank) u j).val)
      (fun _=>DescentFallbackPeriod.Projected.Receiver.matrixBefore B.frame.basis short) paid
      (host v) hi (ix j)=recordedBoard B snap v hi j := by
  have neighbor (v : input.V) (j : Fin (A).degree) := Recorded.peer_at (input:=input) v j
  have reservation (v : input.V) (j l : Fin (A).degree) (s : Fin 6) :=
    Recorded.paddedValue_at (b:=field) (reset:=B) v j l s
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
  rcases B with ⟨ct,rfl,fit₀,order,eq_,Z₀,T₀,age,date,extent,tickets,unit,dimension,tape,board,
    frame,listed,raw,geometry,hubs,valid,grain,wire,atoms,branch,capacity⟩
  subst order
  let digits:=S.resetInputDigits ctl.base ctl.radix i
  let groups:=Fin.valEmbedding (n:=S.groupCount i)
  let large:=compact.trans (Fin.castLEEmb ready.host)
  refine GroupStage.issued_padded_board phase S ready digits oldOrder Z₀ T₀ frame groups compact
    ready.host snap.word (ranks snap.chart (2^(GroupStage.depthBound D n f g))
      (GroupStage.depthBound D n f g+2) snap.memory) stencil _ marks _ own neighbor marked
      ?_ v hi j
  intro u q l ax
  refine (reservation u q l ax).trans ?_
  dsimp only
  unfold GroupStage.peerData
  have sameKey : large.trans Fin.valEmbedding = compact.trans Fin.valEmbedding := by ext; rfl
  rw [sameKey]
  cases DescentGroupPeerOrder.hostRoster phase (compact.trans Fin.valEmbedding) u q <;> cases DescentGroupPeerOrder.hostRoster phase (compact.trans Fin.valEmbedding) u l <;> rfl

/-- The physical row equality returned by the packet gather can be used
directly as the public socket's measured matrix. -/
theorem recorded_public_snapshot
    (stencil : Fin H→Block c→Fin L→ℕ)
    (marks : Fin H→Block c→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap))
    (own : ∀v hi j,stencil (host v) hi j=snap.word (here v hi j))
    (marked : ∀v hi j l,marks (host v) hi j l=
      signedPanel (A) native S input.valid names (here v hi j) l)
    (v : input.V) (hi : Block c) (data : RowData (A).degree L (A).cap field)
    (gathered : ∀j,data j=RootSources.paddedRow stencil next marks (fun u j=>((rank) u j).val)
      (fun _=>DescentFallbackPeriod.Projected.Receiver.matrixBefore B.frame.basis short) paid
      (host v) hi (ix j)) :
    data=recordedBoard B snap v hi := by
  funext j
  exact (gathered j).trans (recorded_padded_board B snap stencil marks own marked v hi j)

/-- When the native row is read from the reached snapshot itself, its two
stencil identities come directly from that snapshot. -/
theorem snapshot_matrix (v : input.V) (hi : Block c) (data : RowData (A).degree L (A).cap field)
    (gathered : ∀j,data j=RootSources.paddedRow snap.stencil next snap.marks (fun u j=>((rank) u j).val)
      (fun _=>DescentFallbackPeriod.Projected.Receiver.matrixBefore B.frame.basis short) paid
      (host v) hi (ix j)) :
    data=recordedBoard B snap v hi :=
  recorded_public_snapshot B snap snap.stencil snap.marks snap.stencilRead snap.markRead v hi data gathered

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
