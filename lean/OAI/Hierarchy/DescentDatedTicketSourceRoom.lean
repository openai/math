import OAI.Hierarchy.DescentDatedOperandPipelineTotal
import OAI.Hierarchy.DescentDatedOperandHeaderPair
import OAI.Hierarchy.DescentDatedOperandNativePreparation

namespace OAI
/-! # Every original selector reads only banks physically allocated before it -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentRawCablePanel DescentHaloWalkRAM
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentOrdinaryAtomFieldRAM
open DescentOperandStateBanks ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor : ℕ)
local notation "l₀" => v.resolver
local notation "g₀" => v.ticketReadGeometry
local notation "a" => (l₀).size+2
local notation "b" => v.bornBook.bits
local notation "N" => (l₀).nodes
local notation "M" => (l₀).lanes
local notation "d" => v.operandShortBits
local notation "R" => v.originChart
local notation "routed₀" => v.routedStart floor
local notation "origin₀" => v.originPortFloor floor
local notation "out₀" => v.originPortEnd floor
local notation "mouth₀" => v.originMouthEnd floor
local notation "old₀" => v.operandOldHeaderStart floor
local notation "new₀" => v.operandMouthHeaderStart floor
local notation "retile₀" => v.operandHeaderEnd floor
local notation "cast₀" => v.headTransferEnd floor
local notation "first₀" => v.operandRootBase floor
local notation "end₀" => v.preparedUntil floor

/-- Public lower bounds needed even when the native program receives a malformed word. -/
theorem ticket_source_order :
    routed₀≤origin₀ ∧ origin₀≤out₀ ∧ out₀ ≤ mouth₀ ∧ mouth₀≤old₀ ∧
      old₀≤new₀ ∧ new₀≤retile₀ ∧ retile₀≤cast₀ ∧ cast₀≤first₀ ∧ first₀≤end₀ :=by
  have r : routed₀≤origin₀:=by
    change routed₀≤(R).finish routed₀
    rw [DescentOrdinaryOriginMask.Return.affine];exact Nat.le_add_right ..
  have dep : mouth₀≤v.operandPathStart floor:=by
    rw [operandPathStart,DescentDatedOperandPages.affine];exact Nat.le_add_right ..
  have pa : v.operandPathStart floor≤v.operandRankStart floor:=
    (Nat.le_add_right ..).trans (DescentDatedSourcePathDirectory.end_le ..)
  have rank : v.operandRankStart floor≤old₀:=Nat.le_add_right ..
  have head : retile₀≤cast₀:=by rw [v.head_transfer_span];exact Nat.le_add_right ..
  have last : first₀≤end₀:=by
    exact (SortedInput.ceilings (g₀) first₀).1.trans ((SortedInput.ceilings (g₀) first₀).2.1.trans (SortedInput.ceilings (g₀) first₀).2.2)
  exact ⟨r,Nat.le_add_right ..,Nat.le_add_right ..,dep.trans (pa.trans rank),Nat.le_add_right ..,
    Nat.le_add_right ..,head,Nat.le_add_right ..,last⟩

private theorem fits_later {w lo hi : ℕ} {bank : Bank} (bounds : bank.Fits w lo) (order : lo≤hi) : bank.Fits w hi :=
  ⟨bounds.1,bounds.2.1,bounds.2.2.trans order⟩

theorem native_source_room {w : ℕ} (c : v.SignedChart) (A : v.ArgumentEntry) (mat : A.Match v floor)
    (shape : v.VectorShape) (blocks : (l₀).blocks=v.material.blocks) (room : first₀<2^w) :
    SourceRoom (g₀) (v.nativeTicketSources floor c A mat shape blocks) w first₀ :=by
  obtain ⟨e₀,e₁,e₂,e₃,e₄,e₅,e₆,e₇,_⟩:=v.ticket_source_order floor
  have atCast:=e₇.trans_lt room
  have atHead:=e₆.trans_lt atCast
  have atMouth:=e₃.trans_lt (e₄.trans_lt (e₅.trans_lt atHead))
  have atPort:=e₂.trans_lt atMouth
  have atOrigin:=e₁.trans_lt atPort
  have gate (j : Fin 4) (expr : Expr) (fit : expr.Fits w cast₀) : (v.sourceCast floor j expr).Fits w first₀:=by
    have small : (DescentDatedOperandCasts.page v.operandWidth d M j).bits≤d*M:=Nat.mul_le_mul_right _ (v.operandWidth_le j)
    exact ⟨ROM.bank_room (DescentDatedOperandCasts.page v.operandWidth d M) (d*M) cast₀ first₀ j small le_rfl room,
      ProtocolRAMGeneratedWrite.fits_mono _ e₇ fit⟩
  have seen (j : Fin (l₀).jobs) (f : Fin 6) : (v.originAt floor d shape j f).Fits w first₀:=by
    let x:=((l₀).index.symm j).1.cast shape.blocks
    let n:=((l₀).index.symm j).2.1
    have returned:=(R).grid.returned_fits ((R).rowsAt routed₀) x atOrigin
    have port:=DescentOperandFamilyBook.expr_fits (DescentOrdinaryOriginPorts.law (R) d) (R).lanes origin₀
      (finProdFinEquiv (n,f)) (fun _ : Fin 1=>Expr.lookup ((R).returned routed₀ x) .row) (fun _=>⟨returned.1,trivial⟩) atPort
    exact ProtocolRAMGeneratedWrite.fits_mono _ (e₂.trans (e₃.trans (e₄.trans (e₅.trans (e₆.trans e₇))))) port
  have previous (j : Fin (l₀).jobs) (f : Fin 4) : (v.oldHeaderAt floor j f).Fits w cast₀:=by
    have bank:=DescentDatedPriorOperand.from_previous_placed (l₀) v.vector (v.vectorStart floor)
      shape.operands shape.blocks shape.hosts shape.groups shape.lanes (e₀.trans_lt atOrigin)
      ((l₀).index.symm j).1 (page (f.castLE (by decide : 4≤7)) ((l₀).index.symm j).2.2)
    have oldLe:routed₀≤cast₀:=e₀.trans (e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆)))))
    exact ⟨ROM.bank_room (ScalarOperand.pages a N M) _ old₀ cast₀ ((l₀).index.symm j).2.1 le_rfl (e₅.trans e₆) atCast,
      fits_later bank.1 oldLe,trivial⟩
  have born (j : Fin (l₀).jobs) (f : Fin 3) : (v.mouthAt floor A mat shape j f).Fits w cast₀:=by
    let chart:=v.mouthChart mat.newBlocks
    have ret:=chart.placed out₀ (((l₀).index.symm j).2.2.cast (shape.operands.trans mat.newArgs.symm)) f
      (((l₀).index.symm j).1.cast shape.blocks) ((v.mouth_translated floor mat.newBlocks).trans_lt atMouth)
    have cap:chart.endAddress out₀≤cast₀:=(v.mouth_translated floor mat.newBlocks).le.trans (e₃.trans (e₄.trans (e₅.trans e₆)))
    exact ⟨ROM.bank_room (ScalarOperand.pages b N M) _ new₀ cast₀ ((l₀).index.symm j).2.1 le_rfl e₆ atCast,
      fits_later ret.1 cap,trivial⟩
  exact ⟨seen,fun j f=>gate 1 _ (previous j f),fun j f=>gate 2 _ (born j f),
    fun j f i=>gate 0 _ (v.wide_word_fits floor atCast _),fun i=>gate 3 _ (v.narrow_word_fits floor atCast _),
    fun j f i=>gate 0 _ (v.wide_word_fits floor atCast _),fun j f i=>gate 0 _ (v.wide_word_fits floor atCast _),
    fun i=>gate 3 _ (v.narrow_word_fits floor atCast _)⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
