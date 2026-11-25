import OAI.Hierarchy.DescentVenueQuantityState
import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentPaidResetCensus

namespace OAI
/-! # Compact reset count columns from the actual charged applications and retained rows -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentStageEdgeReceipt DescentDenseHostOrder DescentSIMDLookup
open DescentActorRaster DescentPackedZip DescentPaidResidentCount DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 350000
set_option maxRecDepth 32000
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ} {params:ResetRates G S k D n h C f g cut tail}
  {previous:Reached W G q ε S k i z D wire hist} (B:ClosedReset previous params)
  {quant precision H0 H M₀ M w:ℕ} (proved:B.Recorded quant)
  (oldRoom:Fintype.card previous.V≤H0) (nextRoom:Fintype.card B.next.V≤H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans previous.vertex
local notation "rank" => (vertex).trans (Fin.castLEEmb oldRoom)
local notation "rawID" => (Z).rawHostRank T rank
local notation "grains" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T grains
local notation "A" => B.next.placement
local notation "G₁" => S.groupCount (i+1)
local notation "newRank" => B.next.vertex.trans (Fin.castLEEmb nextRoom)
local notation "cc" => (T).commonDepth
local notation "Q" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card
local notation "sparse" => H0*Q
local notation "digits" => S.resetOutputDigits params.base params.radix B.age B.commonDepth
local notation "names" => (Z).resetNames T
local notation "raw" => B.raw
local notation "dense" => ((Z).rawHostRank T vertex).trans Fin.valEmbedding
local notation "ps" => DescentPhysicalOrder.rename ((raw).siteFrom (groupRank (Fin.valEmbedding (n:=G₁)) dense) B.valid.coordinates)
local notation "used" => Fintype.card B.next.V

def payable (root:Fin sparse) (hi:DescentColonies.Block cc) : Cell precision :=
  if found:∃u:(coarse).graph.Site,rawID ((Z).placed T u)=root ∧ (Z).blockId T u=hi then
    (Reset.payee B proved (names found.choose):ℕ) else 0

theorem payable_at (u:(coarse).graph.Site) :
    payable (precision:=precision) B proved oldRoom (rawID ((Z).placed T u)) ((Z).blockId T u)=
      ((Reset.payee B proved (names u):ℕ):Cell precision):=by
  let hit:∃v:(coarse).graph.Site,rawID ((Z).placed T v)=rawID ((Z).placed T u) ∧
      (Z).blockId T v=(Z).blockId T u:=⟨u,rfl,rfl⟩
  rw [payable,dite_eq_left hit,ResetInput.place_unique (Z) T ((rawID).injective hit.choose_spec.1) hit.choose_spec.2]

def quantityDims (precision H0 H M₀ M:ℕ):DescentVenueQuantityPlanes.Dims:=
  ⟨Q,H0,H,G₁,2^k,precision,M₀,M⟩
local notation "dim" => quantityDims B precision H0 H M₀ M
def qtyRank (idx:Fin used):Fin sparse :=rawID ((denseOrder B).symm idx)
def qtySheets (j:Fin Q) (host:Fin H0) (ix:Fin (G₁*2^k)):Cell precision:=
  payable B proved oldRoom (finProdFinEquiv (host,j)) ((digits).symm (finProdFinEquiv.symm ix))

theorem paid_bit (p:DescentColonies.Block k)(u:Fin H)(g:Fin G₁) :
    DescentVenueQuantityPlanes.value (dim) (qtyRank B oldRoom)
      (qtySheets B proved oldRoom) p u g=Census.count (A) (Equiv.refl _) newRank precision u g p :=by
  unfold DescentVenueQuantityPlanes.value
  split
  next ok =>
    let x: B.next.V :=(denseOrder B).symm ⟨u.val,ok⟩
    have actual:newRank x=u:=by
      apply Fin.ext
      change ((denseOrder B) ((denseOrder B).symm _)).val=u.val
      simp
    change DescentScalarBookReshape.book (qtySheets B proved oldRoom) p (rawID x) g=_
    simp only [DescentScalarBookReshape.book,qtySheets,Prod.mk.eta,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
    let hi:=(digits).symm (g,p)
    by_cases hit:∃v:(coarse).graph.Site,rawID ((Z).placed T v)=rawID x ∧ (Z).blockId T v=hi
    · obtain ⟨v,loc,blk⟩:=hit
      have place:=(rawID).injective loc
      have orig:=named_home B v
      change ((A).pos ((ps) v),(A).block ((ps) v))=_ at orig
      rw [place,blk,Equiv.apply_symm_apply] at orig
      change ((A).pos ((ps) v),(A).block ((ps) v))=((g,x),p) at orig
      have atHost : newRank ((A).pos ((ps) v)).2=u :=
        (congrArg (fun y : (Fin G₁ × B.next.V) × DescentColonies.Block k => (newRank) y.1.2) orig).trans actual
      have atGroup : ((A).pos ((ps) v)).1=g := congrArg (fun y : (Fin G₁ × B.next.V) × DescentColonies.Block k => y.1.1) orig
      have atBlock : (A).block ((ps) v)=p := congrArg Prod.snd orig
      have old:=DescentPaidResidentCount.live (A) S B.next.valid (Equiv.refl _) newRank precision ((ps) v)
      have phys:((A).records ((ps) v)).length=Reset.payee B proved (names v):=by
        change ((raw).records ((ps).symm ((ps) v))).length=_
        exact (congrArg (fun y=>((raw).records y).length) ((ps).symm_apply_apply v)).trans (Reset.raw_paid B proved v)
      have out:=payable_at (precision:=precision) B proved oldRoom v
      rw [loc,blk] at out
      have coords : (newRank ((A).pos ((ps) v)).2,((A).pos ((ps) v)).1,(A).block ((ps) v)) =
          (u,g,p) := Prod.ext atHost (Prod.ext atGroup atBlock)
      have evalEq := congrArg (fun t : Fin H × Fin G₁ × DescentColonies.Block k =>
        Census.count (A) (Equiv.refl _) newRank precision t.1 t.2.1 t.2.2) coords
      exact out.trans ((congrArg (fun n : ℕ=>(n:Cell precision)) phys).symm.trans (old.symm.trans evalEq))
    · rw [payable,dite_eq_right hit]
      symm;apply DescentPaidResidentCount.ghost
      rintro ⟨z,az,gz,bz⟩
      obtain ⟨v,rfl⟩:=(ps).surjective z
      have origin:=named_home B v
      change ((A).pos ((ps) v),(A).block ((ps) v))=_ at origin
      have loc:=congrArg (fun p=>p.1.2) origin
      have group:=congrArg (fun p=>p.1.1) origin
      have block:=congrArg Prod.snd origin
      apply hit
      refine ⟨v,congrArg rawID (loc.symm.trans ((newRank).injective (az.trans actual.symm))),?_⟩
      apply (digits).eq_symm_apply.mpr
      exact Prod.ext (group.symm.trans gz) (block.symm.trans bz)
  next absent =>
    symm;apply DescentPaidResidentCount.ghost
    rintro ⟨v,atHost,_,_⟩
    exact absent (by
      have numeric:=congrArg Fin.val atHost
      have limit:=(B.next.vertex ((A).pos v).2).isLt
      change (B.next.vertex ((A).pos v).2).val=u.val at numeric
      omega)

theorem quantity_source (L:DescentVenueQuantityPlanes.Layout) (m:Memory w)
    (fit:DescentVenueQuantityPlanes.Room (dim) L used w)
    (oldPos:0<M₀) (newPos:0<M) (occupied:0<H) (nonempty:0<chunks G₁ M)
    (stored:∀(j:Fin Q) (p:Row H0 (2^cc) M₀),m (L.earlier.base+j.val*(H0*chunks (2^cc) M₀)+(row H0 (2^cc) M₀ p).val)=
      ((data (fun u hi=>payable (precision:=precision) B proved oldRoom (finProdFinEquiv (u,j)) hi) p).val:Word w))
    (count:m L.count.base=(used:Word w))
    (inverse:∀v:B.next.V,m (L.inverse.base+((Z).denseHostRank T rank v).val)=((rawID v).val:Word w)):
    ∃done,(DescentVenueQuantityPlanes.program (dim) L w).Exec m done (DescentVenueQuantityPlanes.ticks (dim) L) ∧
      (∀x(p:Row H G₁ M),done (L.out+x.val*(H*chunks G₁ M)+(row H G₁ M p).val)=
      ((data (fun y g=>Census.count (A) (Equiv.refl _) newRank precision y g x) p).val:Word w)) ∧
      ∀a,a<L.pitch ∨ L.out+2^k*(H*chunks G₁ M)≤a→done a=m a :=by
  have ids (j:Fin used):m (L.inverse.base+j.val)=((qtyRank B oldRoom j).val:Word w):=by
    have found:=inverse ((denseOrder B).symm j)
    rw [dense_physical B oldRoom] at found
    change m (L.inverse.base+((denseOrder B) ((denseOrder B).symm j)).val)=_ at found
    rw [(denseOrder B).apply_symm_apply] at found
    exact found
  have prior (j:Fin Q)(p:Row H0 (G₁*2^k) M₀):m (L.earlier.base+j.val*(H0*chunks (G₁*2^k) M₀)+
      (row H0 (G₁*2^k) M₀ p).val)=((data (qtySheets (precision:=precision) B proved oldRoom j) p).val:Word w):=by
    have step := congrArg (fun n=>L.earlier.base+j.val*(H0*chunks n M₀)) (group_size B)
    exact cast_rows (group_size B) (fun e=>(digits).symm (finProdFinEquiv.symm e))
      (group_number B) (fun u hi=>payable (precision:=precision) B proved oldRoom (finProdFinEquiv (u,j)) hi) m _
      (fun v=>by rw [←step]; exact stored j v) p
  obtain ⟨done,cpu,read,frame⟩:=DescentVenueQuantityPlanes.run (dim) L (qtyRank B oldRoom)
    (qtySheets B proved oldRoom) m fit oldPos newPos (Nat.two_pow_pos _) occupied nonempty prior count ids
  refine ⟨done,cpu,?_,frame⟩
  intro x p
  have plane : DescentVenueQuantityPlanes.value (dim) (qtyRank B oldRoom) (qtySheets B proved oldRoom) x =
      fun y g=>Census.count (A) (Equiv.refl _) newRank precision y g x :=
    funext fun y=>funext fun g=>paid_bit B proved oldRoom nextRoom x y g
  rw [←plane]
  exact read x p

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
