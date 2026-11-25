import OAI.Hierarchy.DescentActorRootOffset
import OAI.Hierarchy.DescentResetActorNext
import OAI.Hierarchy.DescentResetActorDirectory
import OAI.Hierarchy.DescentRecordedActorBits
import OAI.Hierarchy.DescentScalarBookReshape
import OAI.Hierarchy.DescentActorDenseRead

namespace OAI
/-! # The physical reset actor planes at terminal group and block coordinates -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
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

theorem dense_physical (x : B.next.V) :
    ((Z).denseHostRank T oldRank x).val=(B.next.vertex x).val := by
  change ((Z).denseHostRank T oldRank x).val=((Z).denseHostRank T vertex x).val
  exact ((Z).denseHostRank_read T oldRank x).trans ((Z).denseHostRank_read T vertex x).symm

def rack :=fun h=>(ResetInput.rackAt oldRank h).map B.frame.host.symm
def shapes (j : Fin (pool).card) :=((shapeOrd).symm j).val
def physicalSheet (l : Fin (pool).card) (h : Fin H0) (b : Fin (groups*2^k)) : Cell 1 :=
  (Z).sparseActor T oldRank (finProdFinEquiv (h,l)) ((digits).symm (finProdFinEquiv.symm b))

theorem old_sheet (l : Fin (pool).card) (h : Fin H0) (hi : Fin (2^cc)) :
    Recorded.realActor (reset:=B) (shapes B) (rack B previous) l h hi =
      (Z).sparseActor T oldRank (finProdFinEquiv (h,l)) hi := by
  cases installedAt : ResetInput.rackAt oldRank h with
  | none=>simp [Recorded.realActor,rack,ResetInput.sparseActor,installedAt]
  | some v=>simp [Recorded.realActor,rack,ResetInput.sparseActor,shapes,installedAt]

def actualBit (h : Fin H) (g : Fin groups) (x : DescentColonies.Block k) : Cell 1 :=
  if ∃u : B.reblock.result.graph.Site,
    newRank ((A).pos u).2=h ∧ ((A).pos u).1=g ∧ (A).block u=x then 1 else 0

theorem cast_rows {H a n n' m word : ℕ} (same : n=n') (name : Fin n'→Fin n)
    (value : ∀j,(name j).val=j.val) (f : Fin H→Fin n→Cell a) (mem : Memory word) (addr : ℕ)
    (old : ∀p : Row H n m,mem (addr+(row H n m p).val)=((data f p).val:Word word)) :
    ∀p : Row H n' m,mem (addr+(row H n' m p).val)=((data (fun h j=>f h (name j)) p).val:Word word) := by
  subst n'
  have eq : ∀g,name g=g:=fun g=>Fin.ext (value g)
  simpa only [eq] using old

theorem group_size : 2^cc=groups*2^k := by
  simpa using Fintype.card_congr ((digits).trans finProdFinEquiv)

theorem group_number (j : Fin (groups*2^k)) :
    ((digits).symm (finProdFinEquiv.symm j)).val=j.val := by
  exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)

theorem physical_reshape (base out : ℕ) (src : Bank) (mem : Memory w) (hm : 0<M)
    (fit : DescentScalarBookReshape.Room H0 (pool).card groups (2^k) 1 M w base out src)
    (earlier : ∀l (p : Row H0 (2^cc) (M*2^k)),
      mem (src.base+l.val*(H0*chunks (2^cc) (M*2^k))+(row H0 (2^cc) (M*2^k) p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w)) :
    let nrow:=2^k*(N*chunks groups M)
    let state:=DescentScalarBookReshape.result H0 (pool).card groups (2^k) 1 M base out src mem
    (DescentScalarBookReshape.program H0 (pool).card groups (2^k) 1 M base out w src).Exec mem state
      ((4+10*DescentScalarBookReshape.cells H0 (pool).card groups (2^k) 1 M)+(4+nrow*54)) ∧
     (∀b (p:Row N groups M),state (out+b.val*(N*chunks groups M)+(row N groups M p).val)=
       ((data (DescentScalarBookReshape.book (physicalSheet B previous) b) p).val:Word w)) ∧
     ∀u,u<base ∨ out+nrow≤u→state u=mem u := by
  have chunksEq : chunks (2^cc) (M*2^k)=chunks groups M:= by
    rw [group_size B]
    exact DescentSIMDLookup.chunks_group groups M (2^k) hm (by positivity)
  apply DescentScalarBookReshape.run _ _ _ _ _ hm (by positivity) fit
  intro l
  let jof:=fun (j:Fin (groups*2^k))=>(digits).symm (finProdFinEquiv.symm j)
  let rep:=Recorded.realActor (reset:=B) (shapes B) (rack B previous) l
  have input:=cast_rows (group_size B) jof (group_number B) rep mem
    (src.base+l.val*(H0*chunks groups M)) (by simpa only [chunksEq] using earlier l)
  have equal : (fun h j => rep h (jof j)) = physicalSheet B previous l :=
    funext fun h => funext fun j => old_sheet B previous l h (jof j)
  simpa only [equal] using input

theorem at_site (q : B.next.V) (g : Fin groups) (x : DescentColonies.Block k) :
    DescentScalarBookReshape.book (physicalSheet B previous) x (rawID q) g =
      actualBit B nextFit (newRank q) g x := by
  simp only [DescentScalarBookReshape.book,physicalSheet,Prod.mk.eta,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  refine ((Z).sparse_known T oldRank q ((digits).symm (g,x))).trans ?_
  unfold actualBit
  have hit : (Z).emits T q.val ((digits).symm (g,x)) ↔ ∃u : B.reblock.result.graph.Site,
      newRank ((A).pos u).2=newRank q ∧ ((A).pos u).1=g ∧ (A).block u=x := by
    refine (actor_coordinate B q g x).symm.trans ⟨?_,?_⟩
    · rintro ⟨u,addr,blk⟩;exact ⟨u,by simp [addr],by simp [addr],blk⟩
    · rintro ⟨u,host,oldG,blk⟩;exact ⟨u,Prod.ext oldG ((newRank).injective host),blk⟩
  simp only [hit]

theorem no_site (h : Fin H) (absent : used≤h.val) (g : Fin groups) (x : DescentColonies.Block k) :
    actualBit B nextFit h g x=0 := by
  unfold actualBit
  rw [ite_eq_right]
  rintro ⟨u,atRack,_,_⟩
  have eqn:=congrArg Fin.val atRack
  have bound:=(B.next.vertex ((A).pos u).2).isLt
  change (B.next.vertex ((A).pos u).2).val=h.val at eqn
  omega

theorem directory_words (src : Bank) (mem : Memory w)
    (earlier : ∀l (p : Row H0 (2^cc) M),mem (src.base+l.val*(H0*chunks (2^cc) M)+(row H0 (2^cc) M p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w))
    (i : Fin N) (j : Fin (chunks (2^cc) M)) :
    mem (src.base+(rootOffset H0 (pool).card (chunks (2^cc) M) i+j.val))=
      ((data ((Z).sparseActor T oldRank) (i,j)).val:Word w) := by
  obtain ⟨⟨h,l⟩,rfl⟩:=finProdFinEquiv.surjective i
  have eq:=earlier l (h,j)
  have addr:(src.base+l.val*(H0*chunks (2^cc) M)+(row H0 (2^cc) M (h,j)).val)=
      src.base+(rootOffset H0 (pool).card (chunks (2^cc) M) (finProdFinEquiv (h,l))+j.val):= by
    simp only [rootOffset,Equiv.symm_apply_apply,row,finProdFinEquiv_apply_val]
    ring
  rw [←addr,eq]
  apply congrArg (fun e : Cell (1*M)=>(e.val:Word w))
  unfold data
  apply congrArg (encode 1 M)
  funext t
  dsimp
  split
  · apply old_sheet
  · rfl

theorem mount_roots (src roots : Bank) (mem : Memory w)
    (earlier : ∀l (p : Row H0 (2^cc) M),mem (src.base+l.val*(H0*chunks (2^cc) M)+(row H0 (2^cc) M p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) l) p).val:Word w))
    (endSrc : src.base+(pool).card*(H0*chunks (2^cc) M)≤roots.base) (room : roots.base+N<2^w) :
    let fixed:=rootLiteral H0 (pool).card (chunks (2^cc) M)
    let state:=DescentStaticWordColumn.image roots.base fixed mem N
    (DescentStaticWordColumn.program w roots.base fixed N).Exec mem state (4+10*N) ∧
    (∀i : Fin N,state (roots.base+i.val)=(rootOffset H0 (pool).card (chunks (2^cc) M) i:Word w)) ∧
    (∀ (i : Fin N) (j : Fin (chunks (2^cc) M)),state (src.base+(rootOffset H0 (pool).card (chunks (2^cc) M) i+j.val))=
      ((data ((Z).sparseActor T oldRank) (i,j)).val:Word w)) ∧
    ∀j,j<roots.base ∨ roots.base+N≤j→state j=mem j := by
  intro fixed state
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ room,?_,?_,DescentStaticWordColumn.frame _ _ _ _⟩
  · intro i
    refine (DescentStaticWordColumn.read roots.base N fixed mem i.isLt).trans ?_
    simp [fixed,rootLiteral]
  · intro i j
    have core : rootOffset H0 (pool).card (chunks (2^cc) M) i+j.val<
        (pool).card*(H0*chunks (2^cc) M) := by
      let ds:=finProdFinEquiv.symm i
      have a:=ds.1.isLt
      have b:=ds.2.isLt
      have c:=j.isLt
      have hl:ds.2.val*H0+ds.1.val<(pool).card*H0:=by
        calc
          _ < ds.2.val*H0+H0:=Nat.add_lt_add_left a _
          _ = (ds.2.val+1)*H0:=by ring
          _ ≤ (pool).card*H0:=Nat.mul_le_mul_right _ b
      calc
        _ < (ds.2.val*H0+ds.1.val)*chunks (2^cc) M+chunks (2^cc) M:=Nat.add_lt_add_left c _
        _ = (ds.2.val*H0+ds.1.val+1)*chunks (2^cc) M:=by ring
        _ ≤ ((pool).card*H0)*chunks (2^cc) M:=Nat.mul_le_mul_right _ hl
        _ = _:=by ring
    refine (DescentStaticWordColumn.frame roots.base N fixed mem
      (src.base+(rootOffset H0 (pool).card (chunks (2^cc) M) i+j.val)) (Or.inl (by omega))).trans ?_
    exact directory_words B previous src mem earlier i j

def denseOrder : B.next.V ≃ Fin used :=
  Equiv.ofBijective B.next.vertex ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨B.next.vertex.injective,by simp⟩)

private theorem same_chunk {U V G M : ℕ} (x : Fin U→Fin G→Cell 1) (y : Fin V→Fin G→Cell 1)
    (u : Fin U) (v : Fin V) (j : Fin (chunks G M)) (same : ∀g,x u g=y v g) :
    data x (u,j)=data y (v,j) := by
  unfold data
  apply congrArg (encode 1 M)
  funext l
  dsimp
  split <;> simp [same]

private theorem zero_chunk {U G M : ℕ} (x : Fin U→Fin G→Cell 1)
    (u : Fin U) (j : Fin (chunks G M)) (same : ∀g,x u g=0) : data x (u,j)=0:=by
  unfold data
  have all : (fun l : Fin M=>if h:j.val*M+l.val<G then x u ⟨_,h⟩ else 0)=fun _=>0:=by
    funext l;split <;> simp [same]
  rw [all]
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin M=>(0:Cell 1))).val=0
  simp []

/-- A final, physically padded plane for each next block at every real and
ghost host, in group-packed words. Its source is the preceding actual
prefix inverse and regrouped shape raster, with exactly the same lane pitch. -/
theorem dense_planes (lo out : ℕ) (cnt inv src : Bank) (mem : Memory w)
    (fit : (DenseRead.expr (2^k) H (chunks groups M) lo N cnt inv src).Fits w out)
    (srcRoom : 2^k*(N*chunks groups M) ≤ src.size) (cntRoom : 0<cnt.size) (invRoom : used ≤ inv.size)
    (early : cnt.base+cnt.size≤lo ∧ inv.base+inv.size≤lo ∧ src.base+src.size≤lo)
    (count : mem cnt.base=(used:Word w))
    (inverse : ∀u : B.next.V,mem (inv.base+((Z).denseHostRank T oldRank u).val)=((rawID u).val:Word w))
    (earlier : ∀b(p : Row N groups M),mem (src.base+b.val*(N*chunks groups M)+(row N groups M p).val)=
       ((data (DescentScalarBookReshape.book (physicalSheet B previous) b) p).val:Word w))
    (first : lo+DenseRead.cells (2^k) H (chunks groups M) lo N≤out)
    (room : out+2^k*(H*chunks groups M)<2^w) (word : H≤2^w) (live : used<2^w)
    (hasHost : 0<H) (hasChunk : 0<chunks groups M) :
    let decl:=DescentStaticWordColumn.image lo (DenseRead.literals (2^k) H (chunks groups M) lo N) mem
      (DenseRead.cells (2^k) H (chunks groups M) lo N)
    let body:=DenseRead.expr (2^k) H (chunks groups M) lo N cnt inv src
    let done:=ProtocolRAM.image out (2^k*(H*chunks groups M)) body decl
    (DenseRead.proc (2^k) H (chunks groups M) lo N out w cnt inv src).Exec mem done
      ((4+10*DenseRead.cells (2^k) H (chunks groups M) lo N)+(4+2^k*(H*chunks groups M)*(2*body.work+4))) ∧
    (∀b(p : Row H groups M),done (out+b.val*(H*chunks groups M)+(row H groups M p).val)=
      ((data (fun v g=>actualBit B nextFit v g b) p).val:Word w)) ∧
    ∀a,a<lo ∨ out+2^k*(H*chunks groups M)≤a→done a=mem a := by
  let order:=denseOrder B
  let source (j : Fin used) := rawID (order.symm j)
  let x (b : DescentColonies.Block k) (v : Fin N) (j : Fin (chunks groups M)) : Word w :=
    (data (DescentScalarBookReshape.book (physicalSheet B previous) b) (v,j)).val
  have ir (j : Fin used) : mem (inv.base+j.val)=((source j).val:Word w):=by
    have actual:=inverse (order.symm j)
    rw [dense_physical] at actual
    change mem (inv.base+(order (order.symm j)).val)=_ at actual
    simpa [source] using actual
  have data0 (b : DescentColonies.Block k) (h : Fin N) (j : Fin (chunks groups M)) :
      mem (src.base+(b.val*(N*chunks groups M)+h.val*chunks groups M+j.val))=x b h j:=by
    simpa [x,row,finProdFinEquiv_apply_val,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.mul_comm] using earlier b (h,j)
  obtain ⟨issued,done,frame⟩:=DenseRead.run source lo out cnt inv src mem x data0 fit srcRoom cntRoom
    invRoom early count ir first room word live hasHost hasChunk
  refine ⟨issued,?_,frame⟩
  rintro b ⟨h,j⟩
  have rd:=done b h j
  have addr: (DenseRead.seats (2^k) H (chunks groups M) (b,h,j)).val=
      b.val*(H*chunks groups M)+(row H groups M (h,j)).val := by
    simp [DenseRead.seats,row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  rw [addr,←Nat.add_assoc] at rd
  rw [rd]
  by_cases active:h.val<used
  · let u:=order.symm ⟨h.val,active⟩
    have host:newRank u=h:=by
      apply Fin.ext
      change (order (order.symm ⟨h.val,active⟩)).val=h.val
      simp
    rw [DenseRead.dense,dite_eq_left active]
    apply congrArg (fun e : Cell (1*M)=>(e.val:Word w))
    apply same_chunk
    intro g
    exact (at_site B previous nextFit u g b).trans
      (congrArg (fun v => actualBit B nextFit v g b) host)
  · rw [DenseRead.dense,dite_eq_right active,zero_chunk _ _ _ (fun g=>no_site B nextFit h (Nat.le_of_not_gt active) g b)]
    rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
