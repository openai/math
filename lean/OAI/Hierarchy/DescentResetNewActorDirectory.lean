import OAI.Hierarchy.DescentResetAnyActorDirectory
import OAI.Hierarchy.DescentTerminalExecUnique
import OAI.Hierarchy.DescentResetActorPlanes

namespace OAI
/-! # Recovering both native actor directories from the actual published reset shape page -/
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

/-- Start from the real shape-major actor words. Install the public pointer
series, scan the real masks, prefix the occupied racks, and chronologically
scatter each sparse name into its compact ordinal. -/
theorem paid_actor_directory (first : ℕ) (src : Bank) (mem : Memory w) (oldPos : 0<M) (oldBits : M≤w)
    (fromScene : ∀l (p : Row H0 (2^cc) M),
      mem (src.base+l.val*(H0*chunks (2^cc) M)+(row H0 (2^cc) M p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w))
    (srcFits : src.Fits w first) (srcSize : N*chunks (2^cc) M≤ src.size)
    (chunksFit : chunks (2^cc) M≤2^w)
    (room : (⟨first,H0,(pool).card,chunks (2^cc) M⟩ : Layout).endAddress<2^w) :
    let L : Layout:=⟨first,H0,(pool).card,chunks (2^cc) M⟩
    ∃out,(L.program w src).Exec mem out (L.ticks src) ∧
      out L.count.base=(used:Word w) ∧
      (∀v : B.next.V,out (L.inverse.base+((Z).denseHostRank T oldRank v).val)=((rawID v).val:Word w)) ∧
      (∀v : B.next.V,out (L.ranks.base+((rawID v).val))=(((Z).denseHostRank T oldRank v).val:Word w)) ∧
      (∀j : Fin N,out (L.flags.base+j.val)=if ∃v,rawID v=j then 1 else 0) ∧
      ∀a<first,out a=mem a := by
  intro L
  have ⟨sites,start,flagEnd,rankEnd,mid,last,dirEnd,_⟩:=L.ordered
  obtain ⟨rootFit,flagFit,rankFit,_,_⟩:=L.fits room
  let K:=chunks (2^cc) M
  have shapeSize : (pool).card*(H0*K)≤ src.size:=by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,K] using srcSize
  have before : src.base+(pool).card*(H0*K)≤first:=(Nat.add_le_add_left shapeSize _).trans srcFits.2.2
  have one : 1<2^w:=by
    have pos : 0<L.pitch:=Nat.two_pow_pos _
    change L.first+(4*L.pitch+1+4*L.sites)<2^w at room
    omega
  have fitSrc : src.Fits w L.flags.base:=⟨srcFits.1,srcFits.2.1,srcFits.2.2.trans (Nat.le_add_right ..)⟩
  obtain ⟨boot,pointers,scene,frame⟩:=mount_roots B previous src L.roots mem fromScene before
    (by change first+N<2^w; exact start.trans_lt ((by
      change L.first+L.pitch≤L.first+(4*L.pitch+1+4*L.sites)
      omega : L.flags.base≤L.endAddress).trans_lt room))
  have span (j : Fin N) : rootOffset H0 (pool).card K j+K≤ src.size:=by
    let v:=finProdFinEquiv.symm j
    have bnd : v.2.val*H0+v.1.val<(pool).card*H0:=by
      calc
        _ < v.2.val*H0+H0:=Nat.add_lt_add_left v.1.isLt _
        _ = (v.2.val+1)*H0:=by rw [Nat.succ_mul]
        _ ≤ (pool).card*H0:=Nat.mul_le_mul_right _ v.2.isLt
    exact (show rootOffset H0 (pool).card K j+K=((v.2.val*H0+v.1.val)+1)*K by rw [Nat.succ_mul];rfl).le.trans
      ((Nat.mul_le_mul_right K bnd).trans (by simpa only [Nat.mul_assoc] using shapeSize))
  let rom:=DescentStaticWordColumn.image first (rootLiteral H0 (pool).card K) mem N
  obtain ⟨out,exec,inv,count,kept,forward,flags⟩:=(Z).actor_directory_full T oldRank oldPos oldBits L.roots src L.flags L.ranks
    L.scratch L.values L.inverse.base (rootOffset H0 (pool).card K) rom rootFit fitSrc sites span pointers scene flagFit rankFit
    sites sites flagEnd rankEnd mid last (dirEnd.trans_lt room) one chunksFit
  refine ⟨out,boot.then exec,count,inv,forward,flags,?_⟩
  intro a low
  exact (kept a (low.trans_le (Nat.le_add_right ..))).trans (frame a (.inl low))

/-- The unconditional bounded execution and the genuine occupied-vertex
directory agree on one explicitly computed physical memory. -/
theorem paid_actor_result (first : ℕ) (src : Bank) (mem : Memory w) (oldPos : 0<M) (oldBits : M≤w)
    (fromScene : ∀l (p : Row H0 (2^cc) M),
      mem (src.base+l.val*(H0*chunks (2^cc) M)+(row H0 (2^cc) M p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w))
    (srcFits : src.Fits w first) (srcSize : N*chunks (2^cc) M≤ src.size)
    (chunksFit : chunks (2^cc) M≤2^w)
    (room : (⟨first,H0,(pool).card,chunks (2^cc) M⟩ : Layout).endAddress<2^w) :
    let L : Layout:=⟨first,H0,(pool).card,chunks (2^cc) M⟩
    let out:=L.result src mem
    (L.program w src).Exec mem out (L.ticks src) ∧
      out L.count.base=(used:Word w) ∧
      (∀v : B.next.V,out (L.inverse.base+((Z).denseHostRank T oldRank v).val)=((rawID v).val:Word w)) ∧
      (∀v : B.next.V,out (L.ranks.base+((rawID v).val))=(((Z).denseHostRank T oldRank v).val:Word w)) ∧
      (∀j : Fin N,out (L.flags.base+j.val)=if ∃v,rawID v=j then 1 else 0) ∧
      ∀a,a<first ∨ L.endAddress≤a→ out a=mem a := by
  intro L out
  obtain ⟨actual,run,count,inverse,forward,flags,_⟩:=paid_actor_directory B previous first src mem
    oldPos oldBits fromScene srcFits srcSize chunksFit room
  have all:=L.evaluate src mem srcFits chunksFit room
  have same : actual=out:=exec_unique _ mem actual out run all.1
  subst actual
  exact ⟨all.1,count,inverse,forward,flags,all.2.2⟩

/-- Reindex the executed inverse by the public sorted vertex names. -/
theorem paid_actor_inverse (mem : Memory w) (dest : ℕ)
    (saved : ∀v : B.next.V,mem (dest+((Z).denseHostRank T oldRank v).val)=((rawID v).val:Word w))
    (i₀ : Fin used) :
    mem (dest+i₀.val)=((rawID ((denseOrder B).symm i₀)).val:Word w) := by
  have word:=saved ((denseOrder B).symm i₀)
  rw [dense_physical B previous] at word
  change mem (dest+((denseOrder B) ((denseOrder B).symm i₀)).val)=_ at word
  simpa only [Equiv.apply_symm_apply] using word

def paidActorAt (key : Fin H) : Option B.next.V :=
  if h : key.val<used then some ((denseOrder B).symm ⟨key.val,h⟩) else none

theorem paidActorAt_known (fits : used≤H) (v : B.next.V) :
    paidActorAt B ((B.next.vertex v).castLE fits)=some v := by
  have ok : (B.next.vertex v).val<used:=(B.next.vertex v).isLt
  simp only [paidActorAt,Fin.val_castLE,dite_eq_left ok]
  exact congrArg some ((denseOrder B).symm_apply_apply v)

theorem paidActorAt_ghost (key : Fin H) (ghost : used≤key.val) : paidActorAt B key=none:=dite_eq_right (Nat.not_lt.mpr ghost)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
