import OAI.Hierarchy.DescentWidenedRotorBoard
import OAI.Hierarchy.DescentRootObservationWidth
import OAI.Hierarchy.DescentRecordedPublicBoard

namespace OAI
/-! # Public rotor archives from a shared narrow saved packet -/
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

/-- The aggregate recorded matrix is invariant under widening its saved
packet word, at every original matrix position and physical old vertex. -/
theorem recordedBoard_widen {wide : ℕ} (grow:field≤wide)
    (resources:max (max r population) (2^r)<2^field) (v:input.V) (hi:Block c)
    (j:DescentRotorWindowArchive.Input (A).degree L (A).cap) :
    (recordedBoard B (snap.widen grow) v hi j).val=(recordedBoard B snap v hi j).val :=by
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
  rcases B with ⟨ct,rfl,fit₀,order,eq_,Z₀,T₀,age,date,extent,tickets,unit,dimension,tape,board,
    frame,listed,raw,geometry,hubs,valid,grain,wire,atoms,branch,capacity⟩
  subst order
  exact GroupStage.board_widened phase S ready (S.resetInputDigits ctl.base ctl.radix i) oldOrder Z₀ T₀ frame
    (Fin.valEmbedding (n:=S.groupCount i)) (compact.trans (Fin.castLEEmb ready.host)) snap.word
    (ranks snap.chart (2^(GroupStage.depthBound D n f g)) (GroupStage.depthBound D n f g+2) snap.memory)
    snap.wordFits snap.signedFits grow resources v hi j

theorem original_wide_matrix {wide : ℕ} (grow:field≤wide)
    (resources:max (max r population) (2^r)<2^field) (v:input.V) (hi:Block c)
    (data:RowData (A).degree L (A).cap wide)
    (posted:∀j,(data j).val=(recordedBoard B snap v hi j).val) :
    data=recordedBoard B (snap.widen grow) v hi :=by
  funext j
  exact Fin.ext ((posted j).trans (recordedBoard_widen B snap grow resources v hi j).symm)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
