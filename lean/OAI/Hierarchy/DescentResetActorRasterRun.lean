import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentActorRechunk

namespace OAI
/-! # From occupied reset shape cells to the physical successor's packed actor pages -/
namespace Hierarchy.DescentActorRaster
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM

structure Store where
  src : Bank
  roots : Bank
  flags : Bank
  ranks : Bank
  scratch : ℕ
  vals : ℕ
  inverse : Bank
  pitch : ℕ
  reshape : ℕ
  byBlock : Bank
  collect : ℕ
  out : ℕ

namespace Store
def count (L : Store) (N : ℕ) : Bank:=⟨L.ranks.base+N,0⟩
def directory (L : Store) (w N nChunk : ℕ) :=
  ((Flags.emit L.roots L.src L.flags.base N nChunk w).seq (ProtocolRAMEndpointPrefix.exclusive w L.flags.base L.ranks.base N)).seq
    (Inverse.program w L.scratch L.vals L.inverse.base N L.flags L.ranks)
def directoryCost (L : Store) (N nChunk : ℕ) :=
  (4+N*(2*(Flags.poll L.roots L.src nChunk).work+4)+(10+(3+12*N)))+
    ProtocolRAMGeneratedWrite.work N (Inverse.address L.flags L.ranks L.inverse.base N) .row
end Store
end Hierarchy.DescentActorRaster
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open ThreeFlat.RAM.PhysicalProcedure
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentResetAttachments
open DescentDenseHostOrder Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedZip
open DescentActorRaster DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage.Prepare
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
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
variable (previous : Fintype.card input.V≤H0) (nextFit : Fintype.card B.next.V≤H)
local notation "oldRank" => (vertex).trans (Fin.castLEEmb previous)
local notation "newRank" => B.next.vertex.trans (Fin.castLEEmb nextFit)
local notation "shapeOrd" => (Z).shapeOrder T
local notation "N" => H0*(pool).card
local notation "rawID" => (Z).rawHostRank T oldRank
local notation "used" => Fintype.card B.next.V

variable (L : Store) {oldM : ℕ}
local notation "pre" => chunks (2^cc) oldM
local notation "new" => chunks groups M
local notation "pitchBank" => Overlap.outputBank L.pitch ((pool).card*H0) (2^cc) oldM (M*2^k) 1
local notation "pitchEnd" => Overlap.finish L.pitch ((pool).card*H0) (2^cc) oldM (M*2^k) 1
local notation "repack" => Overlap.program L.pitch ((pool).card*H0) (2^cc) oldM (M*2^k) 1 w L.src
local notation "sortGroups" => DescentScalarBookReshape.program H0 (pool).card groups (2^k) 1 M L.reshape L.byBlock.base w pitchBank
local notation "collect" => DenseRead.proc (2^k) H new L.collect N L.out w (L.count N) L.inverse L.byBlock
local notation "fixed" => rootLiteral H0 (pool).card pre
local notation "setup" => DescentStaticWordColumn.program w L.roots.base fixed N

def rasterProgram := ((((setup).seq (L.directory w N pre)).seq repack).seq sortGroups).seq collect

def rasterTicks :=
  (((4+10*N+L.directoryCost N pre)+Overlap.ticks L.pitch ((pool).card*H0) (2^cc) oldM (M*2^k) 1 L.src)+
    ((4+10*DescentScalarBookReshape.cells H0 (pool).card groups (2^k) 1 M)+(4+(2^k*(N*new))*54)))+
    ((4+10*DenseRead.cells (2^k) H new L.collect N)+(4+2^k*(H*new)*(2*(DenseRead.expr (2^k) H new L.collect N (L.count N) L.inverse L.byBlock).work+4)))

/-- All run-time data comes from the already issued shape-major occupancy
planes. Host count, inverse ordinal, padding, and block reassignment are
computed by the displayed fixed procedure. -/
theorem successor_actors_directory (mem : Memory w) (oldPos : 0<oldM) (oldBits : oldM≤w) (newPos : 0<M)
    (fromScene : ∀l (p : Row H0 (2^cc) oldM),
      mem (L.src.base+l.val*(H0*pre)+(row H0 (2^cc) oldM p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w))
    (before : L.src.base+(pool).card*(H0*pre)≤L.roots.base)
    (roots : L.roots.Fits w L.flags.base) (src : L.src.Fits w L.flags.base)
    (nr : N≤L.roots.size) (span : ∀j,rootOffset H0 (pool).card pre j+pre≤L.src.size)
    (flags : L.flags.Fits w L.scratch) (ranks : L.ranks.Fits w L.scratch)
    (nf : N≤L.flags.size) (nd : N≤L.ranks.size) (flagEnd : L.flags.base+N≤L.ranks.base)
    (rankEnd : L.ranks.base+N+1≤L.scratch) (mid : L.scratch+N≤L.vals) (last : L.vals+N≤L.inverse.base)
    (directoryRoom : L.inverse.base+2*N<2^w) (one : 1<2^w) (nChunks : pre≤2^w)
    (pitchStart : L.inverse.base+2*N≤L.pitch) (pitchSrc : L.src.Fits w L.pitch)
    (sourceSize : (pool).card*H0*pre≤L.src.size) (pitchSpace : pitchEnd<2^w)
    (gatherRoom : DescentScalarBookReshape.Room H0 (pool).card groups (2^k) 1 M w L.reshape L.byBlock.base pitchBank)
    (shapeStart : L.pitch≤L.reshape)
    (finalAccess : (DenseRead.expr (2^k) H new L.collect N (L.count N) L.inverse L.byBlock).Fits w L.out)
    (bsize : 2^k*(N*new)≤L.byBlock.size) (isize : used≤L.inverse.size)
    (finalStart : (L.count N).base+(L.count N).size≤L.collect ∧ L.inverse.base+L.inverse.size≤L.collect ∧
      L.byBlock.base+L.byBlock.size≤L.collect)
    (finalTab : L.collect+DenseRead.cells (2^k) H new L.collect N≤L.out)
    (space : L.out+2^k*(H*new)<2^w) (hostWidth : H≤2^w) (countWidth : used<2^w)
    (hasHost : 0<H) (hasChunk : 0<new) :
    ∃done,(rasterProgram (B:=B) (H0:=H0) (H:=H) (M:=M) (oldM:=oldM) (w:=w) L).Exec mem done
      (rasterTicks (B:=B) (H0:=H0) (H:=H) (M:=M) (oldM:=oldM) L) ∧
    (∀b(p : Row H groups M),done (L.out+b.val*(H*new)+(row H groups M p).val)=
      ((data (fun h g=>actualBit B nextFit h g b) p).val:Word w)) ∧
    (∀x,x<L.roots.base→done x=mem x) ∧
    (∀u:B.next.V,done (L.inverse.base+((Z).denseHostRank T oldRank u).val)=((rawID u).val:Word w)) ∧
    done (L.ranks.base+N)=(used:Word w) ∧
    (∀u:B.next.V,done (L.ranks.base+(rawID u).val)=(((Z).denseHostRank T oldRank u).val:Word w)) ∧
    (∀j:Fin N,done (L.flags.base+j.val)=if ∃u:B.next.V,rawID u=j then 1 else 0) := by
  have rgn:=roots.2.2
  have srcEnd:=src.2.2
  have bootSpace:L.roots.base+N<2^w:=by omega
  obtain ⟨booted,rowAddr,rowBit,frame0⟩:=mount_roots B previous L.src L.roots mem fromScene before bootSpace
  let rom:=DescentStaticWordColumn.image L.roots.base fixed mem N
  obtain ⟨compact,dir,inverse,count,frame1,forward_,flags_⟩:=(Z).actor_directory_full T oldRank oldPos oldBits L.roots L.src L.flags L.ranks
    L.scratch L.vals L.inverse.base (rootOffset H0 (pool).card pre) rom roots src nr span rowAddr rowBit flags ranks nf nd
    flagEnd rankEnd mid last directoryRoom one nChunks
  have earlier (l : Fin (pool).card) (p:Row H0 (2^cc) oldM) : compact (L.src.base+l.val*(H0*pre)+(row H0 (2^cc) oldM p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w):=by
    let u:=L.src.base+l.val*(H0*pre)+(row H0 (2^cc) oldM p).val
    have up:(row H0 (2^cc) oldM p).val<H0*pre:=(row H0 (2^cc) oldM p).isLt
    have maxL: (l.val+1)*(H0*pre)≤(pool).card*(H0*pre):=Nat.mul_le_mul_right _ l.isLt
    rw [Nat.succ_mul] at maxL
    have safe:u<L.roots.base:=by dsimp [u];omega
    change compact u=_
    exact (frame1 u (by omega)).trans ((frame0 u (Or.inl safe)).trans (fromScene l p))
  let xs:=Recorded.realActor (reset:=B) (shapes B) (rack B previous)
  obtain ⟨changeLane,newSource,frame2,_⟩:=change_pitch (t:=M*2^k) xs L.pitch L.src compact oldPos pitchSrc sourceSize pitchSpace earlier
  let pitched:=Overlap.result L.pitch ((pool).card*H0) (2^cc) oldM (M*2^k) 1 L.src compact
  obtain ⟨sorted,gathered,frame3⟩:=physical_reshape B previous L.reshape L.byBlock.base pitchBank pitched newPos gatherRoom newSource
  let sortedMem:=DescentScalarBookReshape.result H0 (pool).card groups (2^k) 1 M L.reshape L.byBlock.base pitchBank pitched
  have held (x : ℕ) (h:x<L.pitch):sortedMem x=compact x:=(frame3 x (Or.inl (by omega))).trans (frame2 x (Or.inl h))
  have cnt:sortedMem (L.count N).base=(used:Word w):=(held _ (by change L.ranks.base+N<L.pitch;omega)).trans count
  have rawFits:used≤N:=ResetInput.denseFits Z T oldRank
  have inv (u:B.next.V):sortedMem (L.inverse.base+((Z).denseHostRank T oldRank u).val)=((rawID u).val:Word w):=by
    have small : ((Z).denseHostRank T oldRank u).val < used := ((Z).denseHostRank T oldRank u).isLt
    exact (held _ (by omega)).trans (inverse u)
  obtain ⟨done,reads,frame4⟩:=dense_planes B previous nextFit L.collect L.out (L.count N) L.inverse L.byBlock sortedMem
    finalAccess bsize (Nat.two_pow_pos _) isize finalStart cnt inv gathered finalTab space hostWidth countWidth hasHost hasChunk
  refine ⟨_,?_,reads,?_,?_,?_,?_,?_⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then
      (Procedure.Exec.then
        (Procedure.Exec.then
          (Procedure.Exec.then booted dir) changeLane) sorted) done machine
  · intro x hx
    have foot:=finalStart.1
    exact (frame4 x (Or.inl (by change (L.ranks.base+N)+(L.count N).size≤L.collect at foot;omega))).trans
      ((held x (by omega)).trans ((frame1 x (by omega)).trans (frame0 x (Or.inl hx))))
  · intro u
    have ranked : ((Z).denseHostRank T oldRank u).val < used := ((Z).denseHostRank T oldRank u).isLt
    exact (frame4 _ (.inl (by have foot:=finalStart.2.1;omega))).trans (inv u)
  · have foot:=finalStart.1
    have num : (L.count N).size=1:=rfl
    have idx : (L.count N).base=L.ranks.base+N:=rfl
    exact (frame4 _ (.inl (by omega))).trans cnt
  · intro u
    have j : (rawID u).val < N := (rawID u).isLt
    have foot:=finalStart.1
    have idx : (L.count N).base=L.ranks.base+N:=rfl
    exact (frame4 _ (.inl (by omega))).trans ((held _ (by omega)).trans (forward_ u))
  · intro j
    have upper : L.flags.base+j.val<L.ranks.base := lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) flagEnd
    have foot := finalStart.1
    change L.ranks.base+N+1≤L.collect at foot
    have underCollect : L.flags.base+j.val<L.collect := by omega
    have underPitch : L.flags.base+j.val<L.pitch := by omega
    refine ((frame4 (L.flags.base+j.val) (Or.inl underCollect)).trans
      (held (L.flags.base+j.val) underPitch)).trans ?_
    have recorded := flags_ j
    by_cases hit : ∃ u : B.next.V, rawID u = j
    · rw [ite_eq_left hit]
      exact recorded.trans (ite_eq_left hit)
    · rw [ite_eq_right hit]
      exact recorded.trans (ite_eq_right hit)

theorem successor_actors (mem : Memory w) (oldPos : 0<oldM) (oldBits : oldM≤w) (newPos : 0<M)
    (fromScene : ∀l (p : Row H0 (2^cc) oldM),
      mem (L.src.base+l.val*(H0*pre)+(row H0 (2^cc) oldM p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w))
    (before : L.src.base+(pool).card*(H0*pre)≤L.roots.base)
    (roots : L.roots.Fits w L.flags.base) (src : L.src.Fits w L.flags.base)
    (nr : N≤L.roots.size) (span : ∀j,rootOffset H0 (pool).card pre j+pre≤L.src.size)
    (flags : L.flags.Fits w L.scratch) (ranks : L.ranks.Fits w L.scratch)
    (nf : N≤L.flags.size) (nd : N≤L.ranks.size) (flagEnd : L.flags.base+N≤L.ranks.base)
    (rankEnd : L.ranks.base+N+1≤L.scratch) (mid : L.scratch+N≤L.vals) (last : L.vals+N≤L.inverse.base)
    (directoryRoom : L.inverse.base+2*N<2^w) (one : 1<2^w) (nChunks : pre≤2^w)
    (pitchStart : L.inverse.base+2*N≤L.pitch) (pitchSrc : L.src.Fits w L.pitch)
    (sourceSize : (pool).card*H0*pre≤L.src.size) (pitchSpace : pitchEnd<2^w)
    (gatherRoom : DescentScalarBookReshape.Room H0 (pool).card groups (2^k) 1 M w L.reshape L.byBlock.base pitchBank)
    (shapeStart : L.pitch≤L.reshape)
    (finalAccess : (DenseRead.expr (2^k) H new L.collect N (L.count N) L.inverse L.byBlock).Fits w L.out)
    (bsize : 2^k*(N*new)≤L.byBlock.size) (isize : used≤L.inverse.size)
    (finalStart : (L.count N).base+(L.count N).size≤L.collect ∧ L.inverse.base+L.inverse.size≤L.collect ∧
      L.byBlock.base+L.byBlock.size≤L.collect)
    (finalTab : L.collect+DenseRead.cells (2^k) H new L.collect N≤L.out)
    (space : L.out+2^k*(H*new)<2^w) (hostWidth : H≤2^w) (countWidth : used<2^w)
    (hasHost : 0<H) (hasChunk : 0<new) :
    ∃done,(rasterProgram (B:=B) (H0:=H0) (H:=H) (M:=M) (oldM:=oldM) (w:=w) L).Exec mem done
      (rasterTicks (B:=B) (H0:=H0) (H:=H) (M:=M) (oldM:=oldM) L) ∧
    (∀b(p : Row H groups M),done (L.out+b.val*(H*new)+(row H groups M p).val)=
      ((data (fun h g=>actualBit B nextFit h g b) p).val:Word w)) ∧
    ∀x,x<L.roots.base→done x=mem x := by
  obtain ⟨out,exec,reads,early,_,_,_,_⟩:=successor_actors_directory B previous nextFit L mem oldPos oldBits newPos
    fromScene before roots src nr span flags ranks nf nd flagEnd rankEnd mid last directoryRoom one nChunks pitchStart pitchSrc
    sourceSize pitchSpace gatherRoom shapeStart finalAccess bsize isize finalStart finalTab space hostWidth countWidth hasHost hasChunk
  exact ⟨out,exec,reads,early⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
