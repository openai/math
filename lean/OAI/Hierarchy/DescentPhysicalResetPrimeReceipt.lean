import OAI.Hierarchy.DescentPhysicalResetReceipt

namespace OAI
/-! # Reading the recorded graph on the public reset date's actual input banks -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup DescentPackedExchange DescentPackedColony PackedFlow.Canvas ProtocolRAM
open DescentDatedAddressBook ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p)
variable (payload e nbits tbits : ℕ) (calendar : List ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank)
  (out : ResetOutput) (floor : ℕ)
local notation "a₀" => PhysicalReset.fromCalendar S k tail i G.b p f D payload e nbits tbits calendar addr roster out
local notation "A" => input.placement
local notation "E" => (a₀).estimator floor
local notation "M" => (a₀).lanes
local notation "K" => quota S.rounds
local notation "G₀" => (A).wire*((A).z*G.b)
local notation "B₀" => G₀*(A).cap
local notation "H₀" => S.hostSize i
local notation "R" => S.groupCount i
local notation "tokens" => (fun t : DescentPackedFlowRAM.Slot (2^k) (2*(A).cap)=>addr t.1.val t.2.val)
local notation "geometry" => (a₀).chart floor
local notation "flows" => (a₀).flow floor
local notation "cm" => S.groupWidth k tail i+k
local notation "oldCount" => Fintype.card input.V
local notation "geo" => Setup.plan tokens roster H₀ D (E).high (E).low (E).precision (a₀).short M floor f B₀ K G₀
local notation "rawFlow" => Setup.core tokens roster H₀ D (E).high (E).low (E).precision (a₀).short M floor f B₀ K G₀

theorem calendar_dimension : (E).dim=reset.reset.k :=
  (PhysicalReset.calendar_dim S k tail i G.b p f D payload e nbits tbits calendar addr roster out).trans reset.keyWidth.symm

local notation "equality" => (calendar_dimension (p:=p) (reset:=reset) payload e nbits tbits calendar addr roster out floor)
local notation "xy" => (Equiv.cast (congrArg Block ((equality).trans reset.keyWidth))).trans (S.resetInputDigits ctl.base ctl.radix i)
local notation "name" => ((A).numberedHeader xy input.vertex).site
local notation "order₀" => (name).toEmbedding.trans (Fin.castLEEmb input.valid.host)
local notation "earlier" => PackedFlow.Canvas.loc A name xy f input.valid.host (input.branch.le.trans (le_refl D))
local notation "cells₀" => H₀*chunks R M

theorem calendar_parameters (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (cap : (A).cap=(calendar.take i).prod*256) :
    (a₀).ports=(A).degree ∧ (a₀).hosts=H₀ ∧ (a₀).fullBudget=B₀ ∧ (a₀).classBound=K ∧
    (E).precision=S.localWalshBits p (E).dim f K ∧
    (a₀).successor.middle.stencil=stencilLayout (reset:=reset) (p:=p) E D (2^e) nbits tbits := by
  have hm:(E).dim=cm:=(equality).trans reset.keyWidth
  refine ⟨input.branch.symm,rfl,?_,rfl,?_,?_⟩
  · simp only [input.edges,input.grain,old,gr,cap]
    rfl
  · rw [hm]
    rfl
  · unfold stencilLayout PackedFlow.Padded.stencilBook
    rw [input.branch,reset.commonDepth,hm]
    rfl

include accepted in
theorem prime_input {w : ℕ} (src count : Bank) (mem : Memory w) (native : W.graph.Edge↪ℕ)
    (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (cap : (A).cap=(calendar.take i).prod*256) (branch : G.b≤2^S.capGain)
    (lowBits : k≤(E).low) (safe : src.base+src.size≤floor) (capacity : cells₀≤ src.size)
    (weights : Reads src (fun v g=>encode (E).precision (2^k)
      (fun x=>((A).censusValue order₀ (Equiv.refl _) false v g x:Cell (E).precision))) M mem)
    (oldTokens : ∀t,(tokens t).base+(tokens t).size≤floor ∧ cells₀≤(tokens t).size)
    (chips : ∀t : DescentPackedFlowRAM.Slot (2^k) (2*(A).cap), Reads (tokens t) (fun (v : Fin H₀) g=>PackedFlow.Padded.tokens A native S input.valid
      (Equiv.refl _) name (a₀).short v g t) M mem)
    (oldRoster : roster.base+roster.size≤floor) (slots : H₀*D≤roster.size)
    (rosterWords : ∀v:Fin H₀,∀j:Fin D,mem (roster.base+(v.val*D+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster A name input.valid.host v j):Word w))
    (cutCount : count.base+count.size≤floor) (countRead : mem count.base=(oldCount:Word w))
    (fit : (E).Fits w) (room : 3*(E).dim+(E).precision+2≤w)
    (smooth : decayExponent D<2^w) :
    ∃ (prepare : Procedure w) (ticks : ℕ),
      (a₀).prime floor src count R D w=prepare.seq (((E).header (w:=w)).program.seq ((E).cpu w)) ∧
      (a₀).primeTicks floor R D w=ticks+(4+10*((E).staticEnd-(E).origin)+(E).clock) ∧
      ∃prior,prepare.Exec mem prior ticks ∧
        Loaded (u:=(E).high) (l:=(E).low) (b:=(E).precision) A name xy f K earlier (E).depthRows.base (E).gainRows.base (E).start prior ∧
        Originals (HP:=H₀) (D:=D) (u:=(E).high) (l:=(E).low) (b:=(E).precision) A name xy
          (geometry).first (flows).middle (flows).pitch prior ∧ ∀a<floor,prior a=mem a := by
  have met:=calendar_parameters (p:=p) (reset:=reset) payload e nbits tbits calendar addr roster out floor gr old cap
  let priorCap := (calendar.take i).prod*256
  let priorGrain := S.epochPower^S.priceExponent*(S.grainAt G.b p (i+1)*G.b)
  have grainEq : G₀ = priorGrain := by rw [input.edges,input.grain,old,gr]
  let coreAt (cap grain : ℕ) := Setup.core
    (fun t : DescentPackedFlowRAM.Slot (2^k) (2*cap) => addr t.1.val t.2.val)
    roster H₀ D (E).high (E).low (E).precision (a₀).short M floor f (grain*cap) K grain
  let planAt (cap grain : ℕ) := Setup.plan
    (fun t : DescentPackedFlowRAM.Slot (2^k) (2*cap) => addr t.1.val t.2.val)
    roster H₀ D (E).high (E).low (E).precision (a₀).short M floor f (grain*cap) K grain
  have same : geo = geometry := by
    change planAt (A).cap G₀ = planAt priorCap priorGrain
    rw [cap,grainEq]
  have middleEq : (rawFlow).middle = (flows).middle := by
    change (coreAt (A).cap G₀).middle = (coreAt priorCap priorGrain).middle
    rw [cap,grainEq]
  have pitchEq : (rawFlow).pitch = (flows).pitch := by
    change (coreAt (A).cap G₀).pitch = (coreAt priorCap priorGrain).pitch
    rw [cap,grainEq]
  have hostCount:(E).hosts=H₀*((E).dim+1+D):=rfl
  have match₀:(geo).endAddress=(E).origin:=by rw [same]; rfl
  have match₁:(geo).depthPage=(E).depthRows.base:=by rw [same]; rfl
  have match₂:(geo).gainPage=(E).gainRows.base:=by rw [same]; rfl
  have wide : 2^(E).low=M*2^k := by
    change 2^(E).low=2^((E).low-k)*2^k
    rw [←pow_add,Nat.sub_add_cancel lowBits]
  have positive:0<M:=Nat.two_pow_pos _
  have degreeFit:(A).degree<2^(a₀).short:=by
    rw [input.branch];exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by omega) _)
  obtain ⟨prior,step,arr,keep,frame⟩:=accepted.prepare_initial E equality (le_refl D) tokens roster src count mem
    native gr old branch met.2.2.2.2.1 wide positive degreeFit safe capacity weights oldTokens chips oldRoster slots
    rosterWords cutCount countRead hostCount fit room (by simpa only [input.branch] using smooth) match₀ match₁ match₂
  let preAt (cap grain degree : ℕ) : Procedure w := (Setup.prep
    (fun t : DescentPackedFlowRAM.Slot (2^k) (2*cap) => addr t.1.val t.2.val)
    roster H₀ D (E).high (E).low (E).precision (a₀).short M floor f (grain*cap) K grain src R w).seq
      ((planAt cap grain).prepare (coreAt cap grain) count k degree R M w (E).start)
  let ticksAt (cap grain degree : ℕ) := Setup.ticks H₀ D (E).high (E).low (E).precision (a₀).short M
    floor f (grain*cap) K k R + (planAt cap grain).prepareTicks (coreAt cap grain) k degree R M w
  refine ⟨preAt (A).cap G₀ (A).degree, ticksAt (A).cap G₀ (A).degree, ?_, ?_, prior,step,arr,?_,frame⟩
  · change (preAt priorCap priorGrain D).seq _ = (preAt (A).cap G₀ (A).degree).seq _
    rw [cap,grainEq,input.branch]
  · change ticksAt priorCap priorGrain D + _ = ticksAt (A).cap G₀ (A).degree + _
    rw [cap,grainEq,input.branch]
  · simpa only [same,middleEq,pitchEq] using keep

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
