import OAI.Hierarchy.DescentPhysicalResetPrimeReceipt
import OAI.Hierarchy.DescentPhysicalResetStencil

namespace OAI
/-! # Reading the recorded graph on the public reset date's actual input banks -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup DescentPackedExchange DescentPackedColony PackedFlow.Canvas ProtocolRAM
open DescentDatedAddressBook ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentIssuedFallbackPanel DescentGLPacked DescentGLPacked.BankImage DescentPlainTerminal DescentPlainTerminal.Suffix
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
local notation "HP" => S.hostSize i
local notation "R" => S.groupCount i
local notation "tokens" => (fun t : DescentPackedFlowRAM.Slot (2^k) (2*(A).cap)=>addr t.1.val t.2.val)
local notation "geometry" => (a₀).chart floor
local notation "flows" => (a₀).flow floor
local notation "cm" => S.groupWidth k tail i+k
local notation "oldCount" => Fintype.card input.V
local notation "cc" => reset.terminals.commonDepth
local notation "geo" => Setup.plan tokens roster HP D (E).high (E).low (E).precision (a₀).short M floor f B₀ K G₀
local notation "rawFlow" => Setup.core tokens roster HP D (E).high (E).low (E).precision (a₀).short M floor f B₀ K G₀

local notation "equality" => (calendar_dimension (p:=p) (reset:=reset) payload e nbits tbits calendar addr roster out floor)
local notation "xy" => (Equiv.cast (congrArg Block ((equality).trans reset.keyWidth))).trans (S.resetInputDigits ctl.base ctl.radix i)
local notation "name" => ((A).numberedHeader xy input.vertex).site
local notation "order₀" => (name).toEmbedding.trans (Fin.castLEEmb input.valid.host)
local notation "earlier" => PackedFlow.Canvas.loc A name xy f input.valid.host (input.branch.le.trans (le_refl D))
local notation "cells₀" => HP*chunks R M

local notation "fresh" => (geometry).remixEnd (a₀).payload (a₀).gain (a₀).positive
local notation "physical" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geometry).routedHosts (a₀).high (a₀).low (a₀).bits
local notation "savedAt" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((physical).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation:max "sh" ok:arg => PhysicalReset.calendar_shape S k tail i G.b p f D payload e nbits tbits calendar addr roster out ok

include accepted in
theorem stencil_from_previous_reserved {w : ℕ} (src count hub : Bank) (mem : Memory w) (native : W.graph.Edge↪ℕ)
    (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (cap : (A).cap=(calendar.take i).prod*256) (branch : G.b≤2^S.capGain)
    (lowBits : k≤(E).low) (safe : src.base+src.size≤floor) (capacity : cells₀≤ src.size)
    (weights : Reads src (fun v g=>encode (E).precision (2^k)
      (fun x=>((A).censusValue order₀ (Equiv.refl _) false v g x:Cell (E).precision))) M mem)
    (oldTokens : ∀t,(tokens t).base+(tokens t).size≤floor ∧ cells₀≤(tokens t).size)
    (chips : ∀t : DescentPackedFlowRAM.Slot (2^k) (2*(A).cap), Reads (tokens t) (fun (v : Fin HP) g=>PackedFlow.Padded.tokens A native S input.valid
      (Equiv.refl _) name (a₀).short v g t) M mem)
    (oldRoster : roster.base+roster.size≤floor) (slots : HP*D≤roster.size)
    (rosterWords : ∀v:Fin HP,∀j:Fin D,mem (roster.base+(v.val*D+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster A name input.valid.host v j):Word w))
    (cutCount : count.base+count.size≤floor) (countRead : mem count.base=(oldCount:Word w))
    (fit : (E).Fits w) (room : 3*(E).dim+(E).precision+2≤w)
    (smooth : decayExponent D<2^w) (packing : e≤(E).low-k)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (front : (a₀).PrimeRoom floor src count R D w)
    (back : ((a₀).stencilPhase (sh packing) floor count hub g (2^reset.reset.n)).Room w)
    (low : ℕ) (lowKept : low≤ min floor (E).start) (before : low≤(E).origin)
    (loCount : count.Fits w low) (loHubs : hub.Fits w low) (loRoster : roster.Fits w low)
    (hubSize : HP≤hub.size) (hubWords : ∀v,mem (hub.base+(name v).val)=(((A).hub v).toNat:Word w))
    (stored : (chip).Fits w fresh) (stores : ((1+D)+(E).dim)*HP*2^(E).high≤(chip).size)
    (spectrum : (firstContactBank E).Fits w (savedAt+1)) (depthFit : (E).depthRows.Fits w (savedAt+1))
    (live : 0<B₀) (capBits : 2^((E).dim-cc)*B₀<2^nbits) (levelsFit : (E).dim-cc<2^nbits)
    (one : 1<2^nbits) (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w)
    (hostBits : HP<2^w) (codes : 2*DescentFallbackShapeTable.rows ((E).dim-cc) (2^reset.reset.n)≤2^tbits)
    (positiveD : 0<32*Nat.clog 2 (2*D)) :
    let phase:=(a₀).stencilPhase (sh packing) floor count hub g (2^reset.reset.n)
    ∃(μ : DescentGL.Layout (E).dim) (dst : Memory w), HEq μ reset.frame.basis ∧
      ((a₀).throughStencil (sh packing) floor count hub g (2^reset.reset.n) src R D w).Exec mem dst
        ((a₀).throughStencilTicks (sh packing) floor count hub g (2^reset.reset.n) R D w) ∧
      dst phase.saved=((DescentExterior.matrixCode μ).val:Word w) ∧ (∀x<low,dst x=mem x) ∧
      StencilReservationWords (reset:=reset) E equality D (le_refl D) dst ∧
      phase.S.OldOrder phase.X phase.base phase.bank g cc μ dst ∧
      PackedFlow.Padded.Published (h:=(E).high) (l:=(E).low) (2^e) tbits phase.output order₀
        (fun v hi x=>(2*Stencil.shapeCode ((E).dim-cc) (2^reset.reset.n)
          (fieldsRelative cc (originalCell (reset:=reset) v ((rearrange reset.frame.basis).symm
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) ((equality).trans reset.keyWidth)) x)))))+
          (((A).hub v) || decide ((reset.frame.host v,group (reset.reset.placement.b (reset.frame.host v))
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) ((equality).trans reset.keyWidth)) x)))∈reset.reset.placement.keys)).toNat:ℕ)) dst := by
  obtain ⟨prepare,ticks,code,meter,start⟩:=accepted.prime_input payload e nbits tbits calendar addr roster out floor src count mem native
    gr old cap branch lowBits safe capacity weights oldTokens chips oldRoster slots rosterWords cutCount countRead fit room smooth
  obtain ⟨_,hosts,budget,quotaEq,localBits,book⟩:=calendar_parameters (p:=p) (reset:=reset)
    payload e nbits tbits calendar addr roster out floor gr old cap
  have dimension:(E).dim=cm:=(equality).trans reset.keyWidth
  have localGain:(E).gainBits=gainBits (E).dim f K (S.censusBits p):=by rw [dimension];rfl
  have siteEnd:(geometry).first+HP*2^(E).high≤(E).origin:=by
    have rows:=rows_le HP (E).high
    have many:=Nat.le_mul_of_pos_left (page HP (E).high) (show 0<(E).dim+1 by omega)
    obtain ⟨_,s,t,u,v,x,y⟩:=(geometry).stops
    change (geometry).first+((E).dim+1)*page HP (E).high≤(geometry).totals at s
    change _≤(geometry).endAddress
    omega
  have peerEnd:(flows).middle+D*(flows).pitch≤(E).origin:=by
    have a:(flows).middle+D*(flows).pitch≤(geometry).first:=(geometry).stops.1
    omega
  have wide:HP*2^(E).high≤(flows).pitch:=DescentPackedFlowPublication.Book.pitch_room HP (E).high
  have host:(a₀).hosts=HP:=rfl
  have well:(E).staticEnd<2^w:=((geometry).estimator_range (a₀).payload (a₀).gain (a₀).positive).2.1.trans_lt front.bounded
  have packing':2^(a₀).re*2^e*2^((E).dim-cc)=2^(E).low:=by
    rw [reset.commonDepth]
    exact PhysicalReset.calendar_packing S k tail i G.b p f D payload e nbits tbits calendar addr roster out lowBits packing
  let readsAt (ports : ℕ) : Prop := ∀(v : Fin HP) (j : Fin ports),
    mem (roster.base+(v.val*ports+j.val)) =
      (DescentPackedColony.target (PackedFlow.Padded.roster (D:=ports) A name input.valid.host v j):Word w)
  have peers : readsAt (A).degree := by
    rw [input.branch]
    exact rosterWords
  have rosterSize : HP*(A).degree ≤ (a₀).previousRoster.size := by
    change HP*(A).degree ≤ roster.size
    simpa only [input.branch] using slots
  have physicalPorts : (a₀).ports = D := rfl
  have batchExponent : (a₀).e = e := rfl
  have nativeRun:=accepted.through_stencil_reserved (a₀) floor (sh packing) nbits tbits equality host rfl rfl budget quotaEq book
    src count hub mem low prepare ticks (by simpa only [input.branch] using code)
    (by simpa only [input.branch] using meter) start gr old branch live localBits localGain fit
    (Nat.succ_le_of_lt front.dimensions) front.payload score well ((E).room_of_end front.bounded) siteEnd peerEnd wide back
    lowKept before loCount loHubs loRoster hubSize rosterSize countRead hubWords peers
    stored stores spectrum depthFit packing' capBits levelsFit one headerBits hostBits codes (by simpa only [input.branch] using positiveD)
  simpa only [input.branch, physicalPorts, batchExponent] using nativeRun

include accepted in
theorem stencil_from_previous {w : ℕ} (src count hub : Bank) (mem : Memory w) (native : W.graph.Edge↪ℕ)
    (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (cap : (A).cap=(calendar.take i).prod*256) (branch : G.b≤2^S.capGain)
    (lowBits : k≤(E).low) (safe : src.base+src.size≤floor) (capacity : cells₀≤ src.size)
    (weights : Reads src (fun v g=>encode (E).precision (2^k)
      (fun x=>((A).censusValue order₀ (Equiv.refl _) false v g x:Cell (E).precision))) M mem)
    (oldTokens : ∀t,(tokens t).base+(tokens t).size≤floor ∧ cells₀≤(tokens t).size)
    (chips : ∀t : DescentPackedFlowRAM.Slot (2^k) (2*(A).cap), Reads (tokens t) (fun (v : Fin HP) g=>PackedFlow.Padded.tokens A native S input.valid
      (Equiv.refl _) name (a₀).short v g t) M mem)
    (oldRoster : roster.base+roster.size≤floor) (slots : HP*D≤roster.size)
    (rosterWords : ∀v:Fin HP,∀j:Fin D,mem (roster.base+(v.val*D+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster A name input.valid.host v j):Word w))
    (cutCount : count.base+count.size≤floor) (countRead : mem count.base=(oldCount:Word w))
    (fit : (E).Fits w) (room : 3*(E).dim+(E).precision+2≤w)
    (smooth : decayExponent D<2^w) (packing : e≤(E).low-k)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (front : (a₀).PrimeRoom floor src count R D w)
    (back : ((a₀).stencilPhase (sh packing) floor count hub g (2^reset.reset.n)).Room w)
    (low : ℕ) (lowKept : low≤ min floor (E).start) (before : low≤(E).origin)
    (loCount : count.Fits w low) (loHubs : hub.Fits w low) (loRoster : roster.Fits w low)
    (hubSize : HP≤hub.size) (hubWords : ∀v,mem (hub.base+(name v).val)=(((A).hub v).toNat:Word w))
    (stored : (chip).Fits w fresh) (stores : ((1+D)+(E).dim)*HP*2^(E).high≤(chip).size)
    (spectrum : (firstContactBank E).Fits w (savedAt+1)) (depthFit : (E).depthRows.Fits w (savedAt+1))
    (live : 0<B₀) (capBits : 2^((E).dim-cc)*B₀<2^nbits) (levelsFit : (E).dim-cc<2^nbits)
    (one : 1<2^nbits) (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w)
    (hostBits : HP<2^w) (codes : 2*DescentFallbackShapeTable.rows ((E).dim-cc) (2^reset.reset.n)≤2^tbits)
    (positiveD : 0<32*Nat.clog 2 (2*D)) :
    let phase:=(a₀).stencilPhase (sh packing) floor count hub g (2^reset.reset.n)
    ∃(μ : DescentGL.Layout (E).dim) (dst : Memory w), HEq μ reset.frame.basis ∧
      ((a₀).throughStencil (sh packing) floor count hub g (2^reset.reset.n) src R D w).Exec mem dst
        ((a₀).throughStencilTicks (sh packing) floor count hub g (2^reset.reset.n) R D w) ∧
      dst phase.saved=((DescentExterior.matrixCode μ).val:Word w) ∧ (∀x<low,dst x=mem x) ∧
      phase.S.OldOrder phase.X phase.base phase.bank g cc μ dst ∧
      PackedFlow.Padded.Published (h:=(E).high) (l:=(E).low) (2^e) tbits phase.output order₀
        (fun v hi x=>(2*Stencil.shapeCode ((E).dim-cc) (2^reset.reset.n)
          (fieldsRelative cc (originalCell (reset:=reset) v ((rearrange reset.frame.basis).symm
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) ((equality).trans reset.keyWidth)) x)))))+
          (((A).hub v) || decide ((reset.frame.host v,group (reset.reset.placement.b (reset.frame.host v))
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) ((equality).trans reset.keyWidth)) x)))∈reset.reset.placement.keys)).toNat:ℕ)) dst := by
  intro phase
  obtain ⟨μ,dst,eqn,run,saved,prior,_,order,words⟩:=accepted.stencil_from_previous_reserved payload e nbits tbits
    calendar addr roster out floor src count hub mem native gr old cap branch lowBits safe capacity weights oldTokens
    chips oldRoster slots rosterWords cutCount countRead fit room smooth packing score front back low lowKept before
    loCount loHubs loRoster hubSize hubWords stored stores spectrum depthFit live capBits levelsFit one headerBits hostBits
    codes positiveD
  exact ⟨μ,dst,eqn,run,saved,prior,order,words⟩

include accepted in
theorem actor_panel_from_previous {w : ℕ} (src count hub : Bank) (mem : Memory w) (native : W.graph.Edge↪ℕ)
    (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (cap : (A).cap=(calendar.take i).prod*256) (branch : G.b≤2^S.capGain)
    (lowBits : k≤(E).low) (safe : src.base+src.size≤floor) (capacity : cells₀≤ src.size)
    (weights : Reads src (fun v g=>encode (E).precision (2^k)
      (fun x=>((A).censusValue order₀ (Equiv.refl _) false v g x:Cell (E).precision))) M mem)
    (oldTokens : ∀t,(tokens t).base+(tokens t).size≤floor ∧ cells₀≤(tokens t).size)
    (chips : ∀t : DescentPackedFlowRAM.Slot (2^k) (2*(A).cap), Reads (tokens t) (fun (v : Fin HP) g=>PackedFlow.Padded.tokens A native S input.valid
      (Equiv.refl _) name (a₀).short v g t) M mem)
    (oldRoster : roster.base+roster.size≤floor) (slots : HP*D≤roster.size)
    (rosterWords : ∀v:Fin HP,∀j:Fin D,mem (roster.base+(v.val*D+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster A name input.valid.host v j):Word w))
    (cutCount : count.base+count.size≤floor) (countRead : mem count.base=(oldCount:Word w))
    (fit : (E).Fits w) (room : 3*(E).dim+(E).precision+2≤w)
    (smooth : decayExponent D<2^w) (packing : e≤(E).low-k)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (front : (a₀).PrimeRoom floor src count R D w)
    (back : ((a₀).stencilPhase (sh packing) floor count hub g (2^reset.reset.n)).Room w)
    (low : ℕ) (lowKept : low≤ min floor (E).start) (before : low≤(E).origin)
    (loCount : count.Fits w low) (loHubs : hub.Fits w low) (loRoster : roster.Fits w low)
    (hubSize : HP≤hub.size) (hubWords : ∀v,mem (hub.base+(name v).val)=(((A).hub v).toNat:Word w))
    (stored : (chip).Fits w fresh) (stores : ((1+D)+(E).dim)*HP*2^(E).high≤(chip).size)
    (spectrum : (firstContactBank E).Fits w (savedAt+1)) (depthFit : (E).depthRows.Fits w (savedAt+1))
    (live : 0<B₀) (capBits : 2^((E).dim-cc)*B₀<2^nbits) (levelsFit : (E).dim-cc<2^nbits)
    (one : 1<2^nbits) (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w)
    (hostBits : HP<2^w) (codes : 2*DescentFallbackShapeTable.rows ((E).dim-cc) (2^reset.reset.n)≤2^tbits)
    (positiveD : 0<32*Nat.clog 2 (2*D)) :
    let phase:=(a₀).stencilPhase (sh packing) floor count hub g (2^reset.reset.n)
    ∃(μ : DescentGL.Layout (E).dim) (dst : Memory w), HEq μ reset.frame.basis ∧
      ((a₀).throughStencil (sh packing) floor count hub g (2^reset.reset.n) src R D w).Exec mem dst
        ((a₀).throughStencilTicks (sh packing) floor count hub g (2^reset.reset.n) R D w) ∧
      dst phase.saved=((DescentExterior.matrixCode μ).val:Word w) ∧ (∀x<low,dst x=mem x) ∧
      StencilReservationWords (reset:=reset) E equality D (le_refl D) dst ∧
      phase.S.OldOrder phase.X phase.base phase.bank g cc μ dst ∧
      PackedFlow.Padded.Published (h:=(E).high) (l:=(E).low) (2^e) tbits phase.output order₀
        (realPanel (reset:=reset) ((equality).trans reset.keyWidth) μ nbits tbits) dst :=by
  intro phase
  obtain ⟨μ,dst,eqn,run,saved,prior,reservations,order,table,rows,real⟩:=
    accepted.stencil_from_previous_reserved payload e nbits tbits calendar addr roster out floor src count hub mem native
      gr old cap branch lowBits safe capacity weights oldTokens chips oldRoster slots rosterWords cutCount countRead fit room smooth
      packing score front back low lowKept before loCount loHubs loRoster hubSize hubWords stored stores spectrum depthFit
      live capBits levelsFit one headerBits hostBits codes positiveD
  refine ⟨μ,dst,eqn,run,saved,prior,reservations,order,table,rows,?_⟩
  intro v hi x
  have scalar:=accepted.stencil_cell ((equality).trans reset.keyWidth) μ eqn levelsFit one capBits codes
    live (by unfold quota;omega) (by simpa only [input.branch] using positiveD) v hi x
  rw [real v hi x]
  simp only [Equiv.apply_symm_apply] at scalar
  have castBack : (((realPanel (reset:=reset) ((equality).trans reset.keyWidth) μ nbits tbits v hi x).val:ℕ):Cell tbits) =
      realPanel (reset:=reset) ((equality).trans reset.keyWidth) μ nbits tbits v hi x :=
    Fin.ext (Fin.val_cast_of_lt (realPanel (reset:=reset) ((equality).trans reset.keyWidth) μ nbits tbits v hi x).isLt)
  with_unfolding_all exact (congrArg (fun n : ℕ => (n:Cell tbits)) scalar.symm).trans castBack

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
