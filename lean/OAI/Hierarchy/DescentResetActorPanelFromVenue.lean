import OAI.Hierarchy.DescentCalendarResetIngress
import OAI.Hierarchy.DescentResetCanvasIngressRun
import OAI.Hierarchy.DescentPhysicalResetStencilFromTokens

namespace OAI
/-! The original packed venue runs through reset intake, the estimator and the issued actor panel. -/
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

include accepted in
theorem actor_panel_from_venue {w : ℕ} (count : Bank) (mem : Memory w)
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
      PackedFlow.Padded.Published (h:=(E).high) (l:=(E).low) (2^e) tbits phase.output order₀
        (realPanel (reset:=reset) ((equality).trans reset.keyWidth) μ nbits tbits) dst := by
  obtain ⟨oldPrecision,newPrecision⟩:=PhysicalReset.calendar_ingress_precision input tail p f payload e nbits tbits
    calendar io.wire io.roster out ctl.height reset.age.le gr old branch oldWidth
  obtain ⟨exec,srcFit,rows,weights,chips,rosterFit,rosterSize,rosterWords,hubFit,hubSize,hubWords,cntFit,cnt,frame⟩:=
    DescentResetCanvasIngress.stage_front input input.valid.host io out.funded.oldLanes (pre).lanes
      (pre).short out.funded.precision (pre).bits base count mem seen countFit countRead wireRoom oldLanes
      oldPrecision newPrecision ingressRoom
  obtain ⟨afterSigned,afterAtoms,afterAmount⟩:=(L).order base
  have lower : base≤floor:=(afterSigned.trans afterAtoms).trans afterAmount
  have before : base≤(E).origin:=lower.trans ((a₀).occupied floor).1
  have estimatorBegin : (geometry).endAddress≤(E).start :=
    ((geometry).estimator_prefix (a₀).payload (a₀).gain (a₀).positive).trans (Nat.le_add_right ..)
  have lowKept : base≤ min floor (E).start:=le_min lower (before.trans estimatorBegin)
  have token_eq (t : Fin (2^k)×Fin (2*(A).cap)) : addr t.1.val t.2.val=(L).tokens base t :=
    (L).tokenAt_slot base t.1 t.2
  have previous:=(accepted.actor_panel_from_previous payload e nbits tbits calendar addr io.roster out floor
    src count hub ((enter w).image mem) (input.order.trans Fin.valEmbedding) gr old cap branch lowBits
    srcFit.2.2 rows weights
    (fun t=>by dsimp only; rw [token_eq t]; exact ⟨(chips t).1.2.2,(chips t).2.1⟩)
    (fun t=>by dsimp only; rw [token_eq t]; exact (chips t).2.2)
    (rosterFit.2.2.trans lower) rosterSize rosterWords (cntFit.2.2.trans lower) cnt
    fit room smooth packing score front back base lowKept before cntFit hubFit rosterFit hubSize hubWords
    stored stores spectrum depthFit live capBits levelsFit one headerBits hostBits codes positiveD)
  obtain ⟨μ,dst,choice,run,savedWord,kept,rest⟩:=previous
  refine ⟨μ,dst,choice,?_,savedWord,fun x hx=>(kept x hx).trans (frame x (.inl hx)),rest⟩
  exact Procedure.Exec.then @exec @run


end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
