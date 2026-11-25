import OAI.Hierarchy.DescentTerminalBookExteriorCount
import OAI.Hierarchy.DescentNamedFrozenPublicRank

namespace OAI
/-! The sixth local book field at a public pin of a reached named branch. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))



open DescentTerminalGraphPositions DescentTerminalCableOrder DescentTerminalLocalPortBook DescentSharedCableNames DescentColonies
open ThreeFlat.Routing
local notation "retained" => S.groupWidth k tail S.length+k
local notation "O" => leafOrder X G S b hp base width
local notation "placement" => b.target.placement
local notation "native" => b.target.order.trans Fin.valEmbedding
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount S.length)) (b.target.vertex.trans Fin.valEmbedding))
local notation "pinRank" v => (densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding
local notation "operand" v => leafOperands X G S b hp base v
local notation "calendar" => fun g row => ((S.resetInputDigits base radix S.length).symm (g,row)).val
local notation "scale" => ((placement).z*G.b)/p

theorem book_public_entry (room:j ≤ retained) (whole:p∣s) (grains:p∣(placement).z*G.b)
    (v:(net).Site) (pin:Attached net v) (chunk:Fin (poolBatchCount (s*1) p))
    (g : Order.Group O (b.target.home v)) (public_:g.val=none)
    (nm:Order.At O (b.target.home v) g) (label:nm.val=.inr ⟨pin.val,chunk⟩)
    (board:Board (placement).degree (S.groupCount S.length) (2^k) (placement).cap)
    (resident:Board.Resident (p:=p) placement (b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)) S b.target.valid native names (b.target.home v) board)
    (arity : ℕ)
    (slot : (DescentTerminalGraphRows.number net p v (operand v) ⟨.inr pin,chunk⟩).val < arity) :
    (board.directory arity scale (s/p) (2^retained) calendar).address
      (finProdFinEquiv (((placement).pos v).1,(placement).block v))
      ⟨(DescentTerminalGraphRows.number net p v (operand v) ⟨.inr pin,chunk⟩).val,slot⟩ =
      some (0,(Order.inGroup O (b.target.home v) g nm).val) := by
  have parts : poolBatchCount (s*1) p=s/p := by
    have eqn:=DescentTerminalGraphVolume.exact_pieces p s hp whole
    rw [Nat.mul_one]
    simpa only [Nat.mul_div_cancel _ hp] using congrArg (·/p) eqn
  have small : chunk.val < s/p:=chunk.isLt.trans_eq parts
  have clip : (chunk.val+1)*p ≤ s*1 := by
    have h:=Nat.mul_le_mul_right p (Nat.succ_le_of_lt small)
    simpa only [Nat.div_mul_cancel whole,Nat.mul_one] using h
  have ordinal : (Finset.univ.filter (fun z:Attached net v=>(pinRank v) z < (pinRank v) pin)).card=
      densePin X G S b hp base v pin := by
    have h:=DescentTerminalCohortRanks.earlier (densePinEquiv X G S b hp base v) (pinRank v) (fun _=>rfl) 1 pin
    simpa [ProtocolRAMPortRanks.«prefix»,densePin_read X G S b hp base] using h
  have offset:=DescentTerminalPointerDigits.exterior_digit placement native S b.target.valid names v b.target.valid.coordinates
    (pinRank v) hp scale (Nat.div_mul_cancel grains).symm 0 (s/p) ∅ pin (densePin X G S b hp base v pin) chunk.val
    ordinal (fun _=>parts) clip
  have cell : (DescentTerminalGraphRows.number net p v (operand v) ⟨.inr pin,chunk⟩).val =
      board.internal scale ((placement).pos v).1 ((placement).block v)+densePin X G S b hp base v pin*(s/p)+chunk.val := by
    rw [Board.internal,resident.signed v rfl]
    exact Nat.add_right_cancel offset.symm
  rw [board.public_read arity scale (s/p) (2^retained) calendar _ _ _ (densePin X G S b hp base v pin) chunk.val small cell,
    resident_public_name X G S b hp base width room whole v pin g public_ nm chunk label]
  simp only [activeAt,Equiv.apply_symm_apply]

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
