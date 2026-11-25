import OAI.Hierarchy.DescentIssuedQuantityPlanes
import OAI.Hierarchy.DescentVenueQuantityAny
import OAI.Hierarchy.DescentTerminalExecUnique

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


local notation "shape" => quantityDims B 1 H0 H M₀ M

theorem actor_plane_bit (x:DescentColonies.Block k)(h:Fin H)(g:Fin G₁):
    DescentVenueQuantityPlanes.value (shape) (qtyRank B oldRoom) (physicalSheet B oldRoom) x h g=
      actualBit B nextRoom h g x:=by
  unfold DescentVenueQuantityPlanes.value
  split
  next ok=>
    let u:=(denseOrder B).symm ⟨h.val,ok⟩
    have atHost:newRank u=h:=by
      apply Fin.ext
      change ((denseOrder B) ((denseOrder B).symm _)).val=h.val
      simp
    exact (at_site B oldRoom nextRoom u g x).trans (congrArg (fun j=>actualBit B nextRoom j g x) atHost)
  next absent=>exact (no_site B nextRoom h (Nat.le_of_not_gt absent) g x).symm

theorem actor_quantity_source (L:DescentVenueQuantityPlanes.Layout) (m:Memory w)
    (fit:DescentVenueQuantityPlanes.Room (shape) L used w)
    (oldPos:0<M₀) (newPos:0<M) (occupied:0<H) (nonempty:0<chunks G₁ M)
    (stored:∀(j:Fin Q)(p:Row H0 (2^cc) M₀),m (L.earlier.base+j.val*(H0*chunks (2^cc) M₀)+(row H0 (2^cc) M₀ p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w))
    (count:m L.count.base=(used:Word w))
    (inverse:∀v:B.next.V,m (L.inverse.base+((Z).denseHostRank T rank v).val)=((rawID v).val:Word w)):
    ∀x(p:Row H G₁ M),DescentVenueQuantityPlanes.image (shape) L m (L.out+x.val*(H*chunks G₁ M)+(row H G₁ M p).val)=
      ((data (fun h g=>actualBit B nextRoom h g x) p).val:Word w):=by
  have ids (j:Fin used):m (L.inverse.base+j.val)=((qtyRank B oldRoom j).val:Word w):=by
    have found:=inverse ((denseOrder B).symm j)
    rw [dense_physical B oldRoom] at found
    change m (L.inverse.base+((denseOrder B) ((denseOrder B).symm j)).val)=_ at found
    rw [(denseOrder B).apply_symm_apply] at found
    exact found
  have prior (j:Fin Q)(p:Row H0 (G₁*2^k) M₀):m (L.earlier.base+j.val*(H0*chunks (G₁*2^k) M₀)+
      (row H0 (G₁*2^k) M₀ p).val)=((data (physicalSheet B oldRoom j) p).val:Word w):=by
    have step := congrArg (fun n=>L.earlier.base+j.val*(H0*chunks n M₀)) (group_size B)
    have sheet : Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j =
        fun u hi=>(Z).sparseActor T rank (finProdFinEquiv (u,j)) hi :=
      funext fun u=>funext fun hi=>old_sheet B oldRoom j u hi
    exact cast_rows (group_size B) (fun e=>(digits).symm (finProdFinEquiv.symm e))
      (group_number B) (fun u hi=>(Z).sparseActor T rank (finProdFinEquiv (u,j)) hi) m _
      (fun v=>by
        rw [←step]
        simpa only [sheet] using stored j v) p
  obtain ⟨done,cpu,read,_⟩:=DescentVenueQuantityPlanes.run (shape) L (qtyRank B oldRoom)
    (physicalSheet B oldRoom) m fit oldPos newPos (Nat.two_pow_pos _) occupied nonempty prior count ids
  have unique_:=ProtocolRAM.exec_unique _ m done _ cpu (DescentVenueQuantityPlanes.any (shape) L m fit).1
  intro x p
  have plane : DescentVenueQuantityPlanes.value (shape) (qtyRank B oldRoom) (physicalSheet B oldRoom) x =
      fun h g=>actualBit B nextRoom h g x :=
    funext fun h=>funext fun g=>actor_plane_bit B oldRoom nextRoom x h g
  change done=DescentVenueQuantityPlanes.image (shape) L m at unique_
  rw [←unique_,←plane]
  exact read x p

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
