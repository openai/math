import OAI.Hierarchy.DescentResetNewActorDirectory
import OAI.Hierarchy.DescentResetDenseOperand

namespace OAI
/-! # Packed sparse operands through the actual successor actor directory -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentResetAttachments
open DescentDenseHostOrder Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedZip
open DescentActorRaster DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage.Prepare
open scoped Classical Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "raw" => B.raw
local notation "A" => B.next.placement
local notation "groups" => S.groupCount (i+1)
local notation "dense" => ((Z).rawHostRank T vertex).trans Fin.valEmbedding
local notation "rawSite" => (raw).siteFrom (groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "board" => blocks B
local notation "installed" => (Z).actualRecord T vertex

local notation "cc" => (T).commonDepth
local notation "C₀" => GroupStage.depthBound D n f g
local notation "pool" => DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) C₀
variable {H0 H M w : ℕ}
variable (previous : Fintype.card input.V≤H0)
local notation "oldRank" => (vertex).trans (Fin.castLEEmb previous)
local notation "shapeOrd" => (Z).shapeOrder T
local notation "N" => H0*(pool).card
local notation "rawID" => (Z).rawHostRank T oldRank
local notation "used" => Fintype.card B.next.V


open DescentResetNewActorDirectory

/-- Read any stored sparse operand in compact successor order using the recovered count
and inverse. The identical physical prefix handles every operand width. -/
theorem paid_dense_operand {field groups₀ lanes : ℕ} (first : ℕ)
    (cnt inv : Bank) (expr : Expr) (m : Memory w)
    (values : Fin N→Fin groups₀→Cell field) (words : Source expr values lanes m)
    (costFit : expr.Fits w first) (cf : cnt.Fits w first) (inf : inv.Fits w first)
    (count : m cnt.base=(used:Word w))
    (inverse : ∀v : B.next.V,m (inv.base+((Z).denseHostRank T oldRank v).val)=((rawID v).val:Word w))
    (usedFits : used<2^w) (hostFits : H≤2^w) (size : used≤ inv.size)
    (available : (⟨first,H,N,chunks groups₀ lanes⟩ : DescentResetDenseOperand.Layout).endAddress<2^w) :
    let L : DescentResetDenseOperand.Layout:=⟨first,H,N,chunks groups₀ lanes⟩
    let compact : Fin H→Fin groups₀→Cell field:=fun key group=>
      match paidActorAt B key with
      | some v=>values (rawID v) group
      | none=>0
    (L.setup w).Exec m (L.mounted m) (4+10*L.size) ∧
      (L.load cnt inv expr).Fits w L.endAddress ∧
      Source (L.load cnt inv expr) compact lanes (L.mounted m) := by
  intro L compact
  have setup:=L.setup_run m available
  have book:=L.books m
  have safe:=L.book_fits cnt inv cf inf available
  have prior (a) (h : a<first) : L.mounted m a=m a:=setup.2.2.2 a (.inl h)
  let name (ix : Fin used):=rawID ((denseOrder B).symm ix)
  have countRead : L.mounted m cnt.base=(used:Word w):=(prior _ (by have:=cf.1;have:=cf.2.2;omega)).trans count
  have names (ix : Fin used) : L.mounted m (inv.base+ix.val)=((name ix).val:Word w):=by
    have small:=ix.isLt.trans_le size
    have below:=inf.2.2
    exact (prior _ (by omega)).trans (paid_actor_inverse B previous m inv.base inverse ix)
  have atStart : Source expr values lanes (L.mounted m):=fun p=>
    (eval_below _ _ m _ costFit prior).trans (words p)
  have after:=DescentResetDenseOperand.source (H:=H) first cnt inv expr (L.mounted m)
    name values atStart L.endAddress book safe countRead names usedFits hostFits size
  refine ⟨setup.1,L.fits safe _ (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) costFit),?_⟩
  have same : DescentResetDenseOperand.dense (H:=H) name values=compact := by
    funext key group
    by_cases live : key.val<used <;> simp [DescentResetDenseOperand.dense,compact,paidActorAt,live,name]
  exact same ▸ after

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
