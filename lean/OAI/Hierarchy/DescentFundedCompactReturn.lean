import OAI.Hierarchy.DescentFundedStageReturn
import OAI.Hierarchy.DescentFundedCensusInvoice
import OAI.Hierarchy.DescentIssuedQuantityPlanes
import OAI.Hierarchy.DescentVenueQuantityState

namespace OAI
/-! # The consecutive native reset and compact per-block census -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentStageEdgeReceipt DescentDenseHostOrder DescentSIMDLookup
open DescentActorRaster DescentPackedZip DescentPaidResidentCount DescentPacking.PackedMatch.Local.Stage
open DescentFundedCensus ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ} {params:ResetRates G S k D n h C f g cut tail}
  {previous:Reached W G q ε S k i z D wire hist} (B:ClosedReset previous params)
  {quant precision H0 H M₀ M w:ℕ} (proved:B.Recorded quant)
  (oldRoom:Fintype.card previous.V≤H0) (nextRoom:Fintype.card B.next.V≤H)
set_option quotPrecheck false
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


variable {wide base fund : ℕ} (count inverse : Bank)
local notation "book" => (⟨Q,H0,2^cc,M₀,precision,wide⟩:Shape)
local notation "b₀" => (book).roof fund
local notation "dims" => quantityDims B precision H0 H M₀ M
local notation "chart" => DescentVenueQuantityPlanes.State.layout dims b₀ (columns book fund) count inverse
local notation "top" => DescentVenueQuantityPlanes.State.roof dims b₀
local notation "num" => Fintype.card B.next.V

/-- Continue the genuine paid reset pass using the retained original directory.
Only two previously written tables are read below its lower bound. -/
theorem compact_funded (m mid : Memory w) (code : Procedure w) (duration : ℕ)
    (run : code.Exec m mid duration) (read : ∀j pos,mid ((book).column fund j+(row H0 (2^cc) M₀ pos).val)=
      ((data (fun v hi=>payable (precision:=precision) B proved oldRoom (finProdFinEquiv (v,j)) hi) pos).val:Word w))
    (frozen : ∀a,a<base ∨ b₀≤a→mid a=m a)
    (initial : base≤fund) (countFit : count.Fits w base) (inverseFit : inverse.Fits w base) (inverseSize : num≤ inverse.size)
    (real : num<2^w) (host : H≤2^w) (oldPos : 0<M₀) (newPos : 0<M)
    (occupied : 0<H) (nonempty : 0<chunks G₁ M) (space : top<2^w)
    (counted : m count.base=(num:Word w))
    (ids : ∀v:B.next.V,m (inverse.base+((Z).denseHostRank T rank v).val)=((rawID v).val:Word w)) :
    ∃done,(code.seq (DescentVenueQuantityPlanes.program dims chart w)).Exec m done
        (duration+DescentVenueQuantityPlanes.ticks dims chart) ∧
      (∀x (pos:Row H G₁ M),done ((chart).out+x.val*(H*chunks G₁ M)+(row H G₁ M pos).val)=
        ((data (fun y g=>Census.count (A) (Equiv.refl _) newRank precision y g x) pos).val:Word w)) ∧
      (∀a,a<base ∨ top≤a→done a=m a) :=by
  have afterBase:fund≤b₀:=(book).room fund
  have finalFloor:b₀≤top:=by rw [DescentVenueQuantityPlanes.State.shift];exact Nat.le_add_right ..
  obtain ⟨fits,stored⟩:=columns_fits book fund (finalFloor.trans_lt space)
  have bump (a : Bank) (prior:a.Fits w base) : a.Fits w b₀ :=
    ⟨prior.1,prior.2.1,prior.2.2.trans (initial.trans afterBase)⟩
  have bytes: (dims).shapes*(dims).oldHosts*chunks ((dims).groups*(dims).blocks) (dims).oldLanes≤(columns book fund).size:=by
    change Q*H0*chunks (G₁*2^k) M₀≤_
    rw [←group_size B,Nat.mul_assoc]
    exact stored
  have room:=DescentVenueQuantityPlanes.State.room dims b₀ (columns book fund) count inverse fits
    (bump _ countFit) (bump _ inverseFit) bytes inverseSize real host newPos (Nat.two_pow_pos _) space
  have nsize:0<count.size:=Nat.two_pow_pos _
  have low : count.base<base:=by have e:=countFit.2.2;omega
  have one : mid count.base=(num:Word w):=(frozen _ (.inl low)).trans counted
  have two (v:B.next.V) : mid (inverse.base+((Z).denseHostRank T rank v).val)=((rawID v).val:Word w):=by
    apply (frozen _ (.inl ?_)).trans (ids v)
    exact (Nat.add_lt_add_left ((((Z).denseHostRank T rank v).isLt).trans_le inverseSize) _).trans_le inverseFit.2.2
  obtain ⟨done,cpu,values,frame⟩:=quantity_source B proved oldRoom nextRoom chart mid room oldPos newPos occupied nonempty
    read one two
  refine ⟨done,(by
    intro labels regs slots machine
    exact Procedure.Exec.then run cpu machine),values,?_⟩
  intro a outside
  rcases outside with early | late
  · exact (frame a (.inl (early.trans_le (initial.trans afterBase)))).trans (frozen a (.inl early))
  · have size : (dims).blocks*((dims).hosts*chunks (dims).groups (dims).lanes)≤DescentVenueQuantityPlanes.State.rounded
          (DescentVenueQuantityPlanes.State.newRows dims) := Nat.le_pow_clog (by decide) _
    exact (frame a (.inr ((Nat.add_le_add_left size _).trans late))).trans (frozen a (.inr (finalFloor.trans late)))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
