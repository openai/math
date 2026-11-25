import OAI.Hierarchy.DescentRecordedCanvas
import OAI.Hierarchy.DescentPackedCanvasMounted
import OAI.Hierarchy.DescentMeasuredResetArena

namespace OAI
/-! # Physically prime a recorded reset from the protected preceding stage -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup DescentPackedExchange DescentPackedColony PackedFlow.Canvas ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (E : EstimatorArena)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "grain" => (A).wire*((A).z*G.b)
local notation "budget" => grain*(A).cap
local notation "R" => S.groupCount i
local notation "owners" => Fintype.card input.V
local notation "HP" => S.hostSize i
local notation "groups" => Equiv.refl (Fin R)
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i

include reset in
theorem census_total_room (digits : Block E.dim≃Fin R×Block k) (name : input.V≃Fin owners)
    (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (localBits : E.precision=S.localWalshBits p E.dim f K)
    (v : Fin owners) : Native.totalWeight ((A).mixerHeader digits name).loads v<2^E.precision := by
  obtain ⟨weights,_,room,_⟩:=(A).original_calibration S digits input.valid p f K ctl.height reset.age.le
    (input.grain.trans gr) (input.edges.trans old) branch (fun _=>0)
  have bound : Native.totalWeight ((A).mixerHeader digits name).loads v≤2^E.dim*budget := by
    erw [Native.totalWeight_eq]
    calc
      _≤∑ _j : Fin (2^E.dim),budget:=Finset.sum_le_sum (fun j _=>by
        simpa [GroupStage.mixerHeader] using weights ((name).symm v) j)
      _=_:=by simp
  have hp : 2^E.dim≤2^(3*E.dim):=Nat.pow_le_pow_right (by decide) (by omega)
  have hb : budget≤budget^2:=Nat.le_self_pow (by decide : (2:ℕ)≠0) budget
  rw [localBits]
  exact (bound.trans (Nat.mul_le_mul hp hb)).trans_lt room

variable {maxPorts M short floor w : ℕ} (dim : E.dim=reset.reset.k)
  (ports : D≤ maxPorts) (tokens : Setup.Tokens k (2*input.placement.cap)) (roster src count : Bank)
local notation "xy" => (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
local notation "name" => ((A).numberedHeader xy input.vertex).site
local notation "rank" => (name).toEmbedding.trans (Fin.castLEEmb input.valid.host)
local notation "P₀" => Setup.plan tokens roster HP maxPorts E.high E.low E.precision short M floor f budget K grain
local notation "C₀" => Setup.core tokens roster HP maxPorts E.high E.low E.precision short M floor f budget K grain
local notation "earlier" => PackedFlow.Canvas.loc A name xy f input.valid.host (input.branch.le.trans ports)
local notation "words" => HP*chunks R M

include dim in
/-- The calendar and the executable agree on the literal beginning of the
geometry, the peer-page pitch and the last directed-flow pointer. -/
theorem numbered_plan (payload : ℕ)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (lane : E.low=laneBits E.dim payload E.precision) :
    PackedFlow.Canvas.numberedReset S k tail i payload p f K budget maxPorts
      floor (2^DescentPackedFlowPublication.Book.pitchBits HP E.high) K (C₀).middle=P₀ := by
  have width:E.dim=S.groupWidth k tail i+k:=dim.trans reset.keyWidth
  have high:E.dim-E.low=E.high:=by change E.high+E.low-E.low=E.high;omega
  simp only [PackedFlow.Canvas.numberedReset,←width,←localBits,←lane,high]
  rfl

include accepted in
theorem prepare_initial (mem : Memory w) (native : W.graph.Edge↪ℕ)
    (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (localBits : E.precision=S.localWalshBits p E.dim f K)
    (lanes : 2^E.low=M*2^k) (positive : 0<M) (valid : (A).degree<2^short)
    (safe : src.base+src.size≤floor) (capacity : words≤ src.size)
    (weights : Reads src (fun v g=>encode E.precision (2^k)
      (fun x=>((A).censusValue rank groups false v g x:Cell E.precision))) M mem)
    (oldTokens : ∀t,(tokens t).base+(tokens t).size≤floor ∧ words≤(tokens t).size)
    (chips : ∀t : DescentPackedFlowRAM.Slot (2^k) (2*input.placement.cap), Reads (tokens t) (fun (v:Fin HP) g=>PackedFlow.Padded.tokens A native S input.valid groups name short v g t) M mem)
    (oldRoster : roster.base+roster.size≤floor) (slots : HP*maxPorts≤roster.size)
    (rosterWords : ∀v:Fin HP,∀j:Fin maxPorts, mem (roster.base+(v.val*maxPorts+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster A name input.valid.host v j):Word w))
    (oldCount : count.base+count.size≤floor) (countRead : mem count.base=(owners:Word w))
    (hostCount : E.hosts=HP*(E.dim+1+maxPorts)) (fit : E.Fits w)
    (room : 3*E.dim+E.precision+2≤w) (smooth : decayExponent (A).degree<2^w)
    (origin : (P₀).endAddress=E.origin) (levels : (P₀).depthPage=E.depthRows.base) (gains : (P₀).gainPage=E.gainRows.base) :
    let pre:=Setup.prep tokens roster HP maxPorts E.high E.low E.precision short M floor f budget K grain src R w
    let t:=Setup.ticks HP maxPorts E.high E.low E.precision short M floor f budget K k R
    ∃dst,(pre.seq ((P₀).prepare C₀ count k (A).degree R M w E.start)).Exec mem dst
      (t+(P₀).prepareTicks C₀ k (A).degree R M w) ∧
      Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name xy f K earlier E.depthRows.base E.gainRows.base E.start dst ∧
      Originals («HP»:=HP) (u:=E.high) (l:=E.low) (D:=maxPorts) (b:=E.precision) A name xy (P₀).first (C₀).middle (C₀).pitch dst ∧
      ∀a<floor,dst a=mem a := by
  let digits:=xy
  have eqDigits:=same_digits (reset:=reset) E dim
  have depth_cast {m m' : ℕ} (eqn : m'=m) (ds : Block m ≃ Fin R × Block k) :
      ((A).numberedHeader ((Equiv.cast (congrArg Block eqn)).trans ds) input.vertex).depth A f =
        ((A).numberedHeader ds input.vertex).depth A f := by
    subst m'
    rfl
  have transported := depth_cast (dim.trans reset.keyWidth) sourceDigits
  have depth (v:input.V) : ((A).mixerHeader digits name).depth A f v≤E.dim := by
    change ((A).numberedHeader digits input.vertex).depth A f v≤E.dim
    rw [congrFun transported v,←accepted.measured.depth v,dim]
    exact reset.reset.placement.depth _
  have full:=census_total_room (reset:=reset) E digits name gr old branch localBits
  have pages : HP*(E.dim+1)+HP*maxPorts=E.hosts := (Nat.mul_add _ _ _).symm.trans hostCount.symm
  have pfit:=rows_le E.hosts E.high
  have last:E.start+E.hosts*2^E.high<2^w:=by
    have preEnd:=E.areas.2.2.2.2.2.1
    have ins:E.start+E.hosts*2^E.high≤E.inputEnd:=Nat.add_le_add preEnd pfit
    exact (ins.trans (E.calendar.pre (E.dim+1))).trans_lt fit.bounded
  have out : E.start+(HP*(E.dim+1)+HP*maxPorts)*2^E.high<2^w:=by rw [pages];exact last
  have «protected»:(P₀).endAddress≤E.start:=by
    rw [origin]; obtain ⟨a,b,c,d,e,_⟩:=E.areas;omega
  have hostRoom:HP<2^w:=by
    have h₁:HP≤HP*(E.dim+1):=Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have h₂:E.hosts≤E.hosts*2^E.high:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega
  have fits : 2*E.dim+1<2^w:=by have h:=Nat.lt_two_pow_self (n:=w);omega
  have look : smallKey E.low E.precision≤w:=by dsimp [smallKey];have:=fit.lookup;omega
  have all:=Setup.emitted A native S input.valid groups name (input_count (reset:=reset) E dim)
    tokens roster src count input.valid.host (input.branch.le.trans ports) floor f K
    E.start mem lanes positive valid safe capacity weights oldTokens chips oldRoster slots rosterWords
    oldCount countRead (by rw [eqDigits];exact full) look (by rw [eqDigits];exact depth)
    hostRoom fits smooth (by omega) «protected» out
  obtain ⟨dst,run,load,orig,keep⟩ := all
  refine ⟨dst,run,?_,?_,keep⟩
  · let result (ds : Block E.dim ≃ Fin R × Block k) (level gain : ℕ) : Prop :=
      Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name ds f K
        (PackedFlow.Canvas.loc A name ds f input.valid.host (input.branch.le.trans ports))
        level gain E.start dst
    change result xy E.depthRows.base E.gainRows.base
    change result (PackedFlow.digits groups (input_count (reset:=reset) E dim)) (P₀).depthPage (P₀).gainPage at load
    rw [eqDigits,levels,gains] at load
    exact load
  · simpa only [eqDigits] using orig

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
