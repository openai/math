import OAI.Hierarchy.DescentResetActorPanelFromVenue

namespace OAI
/-! Original count, roster, hub, and depth words on the same output as the packed actor panel. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup DescentPackedExchange DescentPackedColony PackedFlow.Canvas ProtocolRAM
open DescentDatedAddressBook ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentGLPacked DescentGLPacked.BankImage DescentPlainTerminal DescentPlainTerminal.Suffix
open DescentCompiler DescentPackedZip
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p)
variable (payload e nbits tbits : ℕ) (calendar : List ℕ) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (out : ResetOutput) (base : ℕ)
local notation "A" => input.placement
local notation "HP" => S.hostSize i
local notation "R" => S.groupCount i
local notation "oldCount" => Fintype.card input.V
local notation "cc" => reset.terminals.commonDepth
local notation "B₀" => (A).wire*((A).z*G.b)*(A).cap
local notation "pre" => PhysicalReset.fromCalendar S k tail i G.b p f D payload e nbits tbits calendar io.wire io.roster out
local notation "L" => DescentResetCanvasIngress.datedLayout input HP out.funded.oldLanes (pre).lanes (pre).short out.funded.precision (pre).bits
local notation "addr" => (L).tokenAt base
local notation "floor" => (L).endAddress base
local notation "a₀" => PhysicalReset.fromCalendar S k tail i G.b p f D payload e nbits tbits calendar addr io.roster out
local notation "src" => (L).source base
local notation "E" => (a₀).estimator floor
local notation "hub" => io.hubs
local notation:max "enter" w:arg => (L).phase base w hub (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
local notation "geometry" => (a₀).chart floor
local notation "fresh" => (geometry).remixEnd (a₀).payload (a₀).gain (a₀).positive
local notation "physical" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geometry).routedHosts (a₀).high (a₀).low (a₀).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((physical).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "equality" => (calendar_dimension (p:=p) (reset:=reset) payload e nbits tbits calendar addr io.roster out floor)
local notation "name" => DescentResetSignedTokens.venueNames input
local notation "order₀" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation:max "sh" ok:arg => PhysicalReset.calendar_shape S k tail i G.b p f D payload e nbits tbits calendar addr io.roster out ok

local notation "wide" => S.groupWidth k tail i+k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "peer" => PackedFlow.portAt A ((A).numberedHeader digits input.vertex).site

private theorem canonical_panel {w m M t nbits address : ℕ} (dim : m=wide) (basis : DescentGL.Layout m)
    (same : HEq basis reset.frame.basis) (dst : Memory w)
    (published : PackedFlow.Padded.Published (h:=m) (l:=0) M t address order₀
      (realPanel (reset:=reset) dim basis nbits t) dst) :
    PackedFlow.Padded.Published (h:=S.groupWidth k tail i) (l:=k) M t address order₀
      (realPanel (reset:=reset) rfl reset.frame.basis nbits t) dst := by
  subst m
  obtain rfl := eq_of_heq same
  exact published

private theorem roster_digit (v : input.V) (j : Fin (A).degree) :
    DescentPackedColony.target
        (PackedFlow.Padded.roster (D:=D) A name input.valid.host (order₀ v) (j.cast input.branch))=
      DescentFallbackRankRAM.hostDigit order₀ (peer v j) := by
  have slot : DescentPackedFlowPair.Padded.project (A).degree (j.cast input.branch)=some j := by
    simp [DescentPackedFlowPair.Padded.project,j.isLt]
  unfold PackedFlow.Padded.roster DescentPackedFlowPair.Padded.next
  change DescentPackedColony.target
    ((DescentPackedFlowPair.Padded.project oldCount ((name v).castLE input.valid.host)).bind _)=_
  rw [DescentPackedFlowPair.Padded.project_cast]
  simp only [Option.bind_some,slot]
  change DescentPackedColony.target ((PackedFlow.next A name (name v) j).map (Fin.castLE input.valid.host))=
    DescentFallbackRankRAM.hostDigit order₀ ((PackedFlow.next A name (name v) j).map (name).symm)
  cases found : PackedFlow.next A name (name v) j with
  | none => rfl
  | some u =>
    change u.val=(name ((name).symm u)).val
    rw [Equiv.apply_symm_apply]

include accepted in
theorem actor_panel_from_venue_directory {w : ℕ} (count : Bank) (mem : Memory w)
    (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (cap : (A).cap=(calendar.take i).prod*256) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io out.funded.oldLanes out.funded.precision base
      (input.venueRoster input.valid.host) mem)
    (countFit : count.Fits w base) (countRead : mem count.base=(oldCount:Word w))
    (wireRoom : ∀(x:Block k)(j:Fin (2*(A).cap)),(io.wire x.val j.val).Fits w base ∧
      HP*chunks R out.funded.oldLanes≤(io.wire x.val j.val).size)
    (oldLanes : 0<out.funded.oldLanes) (oldWidth : out.funded.precision=S.censusBits p)
    (ingressRoom : floor<2^w) (lowBits : k≤(E).low)
    (fit : (E).Fits w) (room : 3*(E).dim+(E).precision+2≤w)
    (smooth : decayExponent D<2^w) (packing : e≤(E).low-k)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (front : (a₀).PrimeRoom floor src count R D w)
    (back : ((a₀).stencilPhase (sh packing) floor count hub g (2^reset.reset.n)).Room w)
    (stored : (chip).Fits w fresh) (stores : ((1+D)+(E).dim)*HP*2^(E).high≤(chip).size)
    (spectrum : (firstContactBank E).Fits w (saved+1)) (depthFit : (E).depthRows.Fits w (saved+1))
    (live : 0<B₀) (capBits : 2^((E).dim-cc)*B₀<2^nbits) (levelsFit : (E).dim-cc<2^nbits)
    (one : 1<2^nbits) (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w)
    (hostBits : HP<2^w) (codes : 2*DescentFallbackShapeTable.rows ((E).dim-cc) (2^reset.reset.n)≤2^tbits)
    (positiveD : 0<32*Nat.clog 2 (2*D)) :
    let phase:=(a₀).stencilPhase (sh packing) floor count hub g (2^reset.reset.n)
    ∃(μ : DescentGL.Layout (E).dim) (dst : Memory w), HEq μ reset.frame.basis ∧
      ((enter w).program.seq ((a₀).throughStencil (sh packing) floor count hub g (2^reset.reset.n) src R D w)).Exec mem dst
        ((enter w).ticks+(a₀).throughStencilTicks (sh packing) floor count hub g (2^reset.reset.n) R D w) ∧
      dst phase.saved=((DescentExterior.matrixCode μ).val:Word w) ∧ (∀x<base,dst x=mem x) ∧
      StencilReservationWords (reset:=reset) E equality D (le_refl D) dst ∧
      phase.S.OldOrder phase.X phase.base phase.bank g cc μ dst ∧
      PackedFlow.Padded.Published (h:=S.groupWidth k tail i) (l:=k) (2^e) tbits phase.output order₀
        (realPanel (reset:=reset) rfl reset.frame.basis nbits tbits) dst ∧
      (∀u j,dst (io.roster.base+((order₀ u).val*(A).degree+j.val))=
        (DescentFallbackRankRAM.hostDigit order₀ (peer u j):Word w)) ∧
      (∀u,dst (io.hubs.base+(order₀ u).val)=(((A).hub u).toNat:Word w)) ∧
      dst count.base=(oldCount:Word w) ∧
      ∀v,dst ((E).depthRows.base+(order₀ v).val*(wide+1))=
        (reset.reset.placement.b (reset.frame.host v):Word w) := by
  obtain ⟨μ,dst,choice,run,savedWord,prior,reservations,ord,pub⟩:=
    accepted.actor_panel_from_venue payload e nbits tbits calendar io out base count mem gr old cap branch
      seen countFit countRead wireRoom oldLanes oldWidth ingressRoom lowBits fit room smooth packing score front
      back stored stores spectrum depthFit live capBits levelsFit one headerBits hostBits codes positiveD
  refine ⟨μ,dst,choice,run,savedWord,prior,reservations,ord,
    canonical_panel (reset:=reset) ((equality).trans reset.keyWidth) μ choice dst pub,?_,?_,?_,?_⟩
  · intro u j
    let h:=order₀ u
    let slot:=j.cast input.branch
    have reach : h.val*D+slot.val<HP*D:=by
      simpa only [finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (h,slot)).isLt
    have low:io.roster.base+(h.val*D+slot.val)<base:=
      (Nat.add_lt_add_left (reach.trans_le seen.1.rosterRoom) _).trans_le seen.1.roster.2.2
    have eqn : io.roster.base+((order₀ u).val*(A).degree+j.val)=io.roster.base+(h.val*D+slot.val) :=
      congrArg (fun d=>io.roster.base+(h.val*d+j.val)) input.branch
    rw [eqn,prior _ low]
    exact (seen.2.1.roster h slot).trans (congrArg (fun o=>(DescentPackedColony.target o:Word w))
      (DescentResetCanvasIngress.roster_eq input input.valid.host h slot) |>.trans
      (congrArg (fun n:ℕ=>(n:Word w)) (roster_digit (input:=input) (ctl:=ctl) u j)))
  · intro u
    have low:io.hubs.base+(order₀ u).val<base:=
      (Nat.add_lt_add_left ((order₀ u).isLt.trans_le seen.2.2.2.2.2.1) _).trans_le seen.2.2.2.2.1.2.2
    rw [prior _ low]
    exact (seen.2.2.2.2.2.2.1 (order₀ u)).trans (congrArg (fun n:ℕ=>(n:Word w))
      (DescentHubBits.live A order₀ u))
  · rw [prior _ (by have:=countFit.1;have:=countFit.2.2;omega),countRead]
  · intro v
    obtain ⟨_,_,depth⟩:=reservations
    have dim : (E).dim=wide:=(equality).trans reset.keyWidth
    have address := congrArg (fun n : ℕ => dst ((E).depthRows.base+(order₀ v).val*(n+1))) dim
    exact (address.symm.trans (depth v)).trans
      (congrArg (fun n : ℕ => (n:Word w)) (accepted.measured.depth v).symm)

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
