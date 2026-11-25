import OAI.Hierarchy.DescentResetNewActorDirectory
import OAI.Hierarchy.DescentReachedOriginalNumericFields

namespace OAI
/-! The original source inverse, in the precise row conventions of the public donor numberer. -/
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
set_option hygiene false
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

theorem actual_donor_directory (first : ℕ) (src : Bank) (mem : Memory w) (oldPos : 0<M) (oldBits : M≤w)
    (fromScene : ∀l (p : Row H0 (2^cc) M),
      mem (src.base+l.val*(H0*chunks (2^cc) M)+(row H0 (2^cc) M p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w))
    (srcFits : src.Fits w first) (srcSize : N*chunks (2^cc) M≤ src.size)
    (chunksFit : chunks (2^cc) M≤2^w)
    (room : (⟨first,H0,(pool).card,chunks (2^cc) M⟩ : Layout).endAddress<2^w) :
    let L : Layout:=⟨first,H0,(pool).card,chunks (2^cc) M⟩
    let out:=L.result src mem
    out L.count.base=(used:Word w) ∧
      (∀i:Fin used,out (L.inverse.base+i.val)=((originalCompactName B H0 previous i).val:Word w)) ∧
      used<2^w ∧ used≤L.inverse.size :=by
  intro L out
  have result:=paid_actor_result B previous first src mem oldPos oldBits fromScene srcFits srcSize chunksFit room
  have small : used≤N:=by
    have bound := Fintype.card_le_of_injective (fun act : B.next.V => rawID act) (rawID).injective
    simpa only [Fintype.card_fin] using bound
  have pitch : N≤L.pitch:=Nat.le_pow_clog (by decide) _
  have fit : L.pitch<2^w:=by
    change first+(4*L.pitch+1+4*N)<2^w at room
    omega
  refine ⟨result.2.1,?_,small.trans_lt (pitch.trans_lt fit),small.trans pitch⟩
  intro i
  let dir:=DescentStageEdgeReceipt.dense ((Z).denseHostRank T oldRank)
  let v:=dir.symm i
  have at_ : (Z).denseHostRank T oldRank v=i:=dir.apply_symm_apply i
  have indexEq := congrArg (fun k : Fin used => out (L.inverse.base+k.val)) at_.symm
  have actorEq := (congrArg (fun k : Fin used => originalCompactName B H0 previous k) at_.symm).trans
    (originalCompactName_read B H0 previous v)
  exact (indexEq.trans (result.2.2.1 v)).trans (congrArg (fun j : Fin N => (j.val : Word w)) actorEq.symm)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
