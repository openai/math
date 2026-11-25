import OAI.Hierarchy.DescentRecordedCanvasPreparation

namespace OAI
/-! # The measured GL solver executes on the exact preceding census and signed rows -/

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

variable {maxPorts M short floor w : ℕ} (dim : E.dim=reset.reset.k)
  (ports : D≤ maxPorts) (tokens : Setup.Tokens k (2*input.placement.cap)) (roster src count : Bank)
local notation "xy" => (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
local notation "name" => ((A).numberedHeader xy input.vertex).site
local notation "rank" => (name).toEmbedding.trans (Fin.castLEEmb input.valid.host)
local notation "P₀" => Setup.plan tokens roster HP maxPorts E.high E.low E.precision short M floor f budget K grain
local notation "C₀" => Setup.core tokens roster HP maxPorts E.high E.low E.precision short M floor f budget K grain
local notation "earlier" => PackedFlow.Canvas.loc A name xy f input.valid.host (input.branch.le.trans ports)
local notation "words" => HP*chunks R M

include accepted in
theorem issued_from_previous (mem : Memory w) (native : W.graph.Edge↪ℕ)
    (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (localBits : E.precision=S.localWalshBits p E.dim f K)
    (lanes : 2^E.low=M*2^k) (positive : 0<M) (valid : (A).degree<2^short)
    (safe : src.base+src.size≤floor) (capacity : words≤ src.size)
    (weights : Reads src (fun v g=>encode E.precision (2^k)
      (fun x=>((A).censusValue rank groups false v g x:Cell E.precision))) M mem)
    (oldTokens : ∀t,(tokens t).base+(tokens t).size≤floor ∧ words≤(tokens t).size)
    (chips : ∀t : DescentPackedFlowRAM.Slot (2^k) (2*input.placement.cap), Reads (tokens t) (fun (v : Fin HP) g=>PackedFlow.Padded.tokens A native S input.valid groups name short v g t) M mem)
    (oldRoster : roster.base+roster.size≤floor) (slots : HP*maxPorts≤roster.size)
    (rosterWords : ∀v:Fin HP,∀j:Fin maxPorts, mem (roster.base+(v.val*maxPorts+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster A name input.valid.host v j):Word w))
    (oldCount : count.base+count.size≤floor) (countRead : mem count.base=(owners:Word w))
    (hostCount : E.hosts=HP*(E.dim+1+maxPorts)) (fit : E.Fits w)
    (oldShape : (P₀).endAddress=E.origin ∧ (P₀).depthPage=E.depthRows.base ∧ (P₀).gainPage=E.gainRows.base)
    (smooth : decayExponent (A).degree<2^w) (live : 0<budget)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w) (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    let lower:=Setup.prep tokens roster HP maxPorts E.high E.low E.precision short M floor f budget K grain src R w
    let prepare:=lower.seq ((P₀).prepare C₀ count k (A).degree R M w E.start)
    let t:=Setup.ticks HP maxPorts E.high E.low E.precision short M floor f budget K k R+(P₀).prepareTicks C₀ k (A).degree R M w
    ∃ (prior : Memory w) (μ : DescentGL.Layout E.dim), let dst:=E.image (E.literal prior)
      prepare.Exec mem prior t ∧ HEq μ reset.frame.basis ∧
      (prepare.seq ((E.header (w:=w)).program.seq (E.cpu w))).Exec mem dst
        (t+(4+10*(E.staticEnd-E.origin)+E.clock)) ∧
      (∀a : Fin E.dim,dst (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val:Word w)) ∧
      (∀a : Fin (2^E.dim),dst (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val:Word w)) ∧
      Originals («HP»:=HP) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision) A name xy (P₀).first (C₀).middle (C₀).pitch dst ∧
      (∀a<floor,dst a=mem a) ∧ E.FirstTotals (publicLoad E dim maxPorts ports hostCount) dst ∧
      ∀v,dst (E.depthRows.base+(name v).val*(E.dim+1))=(((A).mixerHeader xy name).depth A f v:Word w) := by
  intro lower prepare t
  obtain ⟨origin,levels,gains⟩:=oldShape
  have hrows : HP*2^E.high≤(C₀).pitch:=DescentPackedFlowPublication.Book.pitch_room HP E.high
  have endSite : (P₀).first+HP*2^E.high≤E.origin := by
    rw [←origin]
    have rows:=rows_le HP E.high
    have many:=Nat.le_mul_of_pos_left (page HP E.high) (show 0<E.dim+1 by omega)
    obtain ⟨_,s,t,u,v,x,y⟩:=(P₀).stops
    change (P₀).first+(E.dim+1)*page HP E.high≤(P₀).totals at s
    omega
  have endFlow : (C₀).middle+maxPorts*(C₀).pitch≤E.origin:=by
    have a : (C₀).middle+maxPorts*(C₀).pitch≤(P₀).first:=(P₀).stops.1
    omega
  have lowOrigin:floor≤E.origin:=by
    obtain ⟨one,two,three,four⟩:=Setup.areas tokens roster HP maxPorts E.high E.low E.precision short M floor f budget K grain
    omega
  have «prefix»:E.origin≤E.start:=by obtain ⟨a,b,c,d,e,_⟩:=E.areas;omega
  have setup:=accepted.prepare_initial E dim ports tokens roster src count mem native gr old branch localBits lanes positive valid
    safe capacity weights oldTokens chips oldRoster slots rosterWords oldCount countRead hostCount fit (by omega) smooth origin levels gains
  obtain ⟨prior,μ,prepared,chosen,run,matrix,perm,original,keep,first,depths⟩:=
    accepted.after_canvas_named E dim mem prepare t maxPorts ports hostCount (P₀).first (C₀).middle (C₀).pitch floor hrows
      (endSite.trans «prefix») (endFlow.trans «prefix») (.inl endSite) (.inl endFlow) setup
      gr old branch live localBits localGain fit stage small score endRoom issue
  exact ⟨prior,μ,prepared,chosen,run,matrix,perm,original,fun a ha=>
    keep a (lt_min_iff.mpr ⟨ha,(ha.trans_le lowOrigin).trans_le «prefix»⟩) (.inl (ha.trans_le lowOrigin)),first,depths⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
