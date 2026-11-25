import OAI.Hierarchy.GridChosenReceiverPrefix
import OAI.Hierarchy.GridReceiverBanks
import OAI.Hierarchy.GridPinArenaRoom
import OAI.Hierarchy.GridReceiverElectionRoom
import OAI.Hierarchy.GridInstalledFit
import OAI.Hierarchy.TraceReceiverRuns

namespace OAI
/-! # The registered and elected prefix on each actual installed receiver stream -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceAdmission GridScale GridThrough GridRegisteredSetting GridInstalledEvaluator GridReceiverDirectory Filter
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}
section PerStream
variable {blk : Block F} {m A w degree stageRate rootRate tariff power : ℕ}
variable {v : TickSelection F (m+1) A w Q loss} (I : Installed blk m A w degree stageRate rootRate v)
variable (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I tariff power)
local notation "l" => (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate)
local notation "arch" => (GridDescription.capacity w)
local notation "gate" => (26*GridDescription.sector w)
local notation "W" => (64*w)
local notation "rails" => (GridControllerSimGeometry.railCount m (l).sideMinusOne (l).bank)

/-- The argument `recv` can be the single padded full receiver used by every
cell. The supplied stream includes this very machine's executable and the
selected trace's actual header and external data. -/
def InstalledPrefix (geom : ElectionRoom I.D l) : Prop :=
  ∀ (recv : Machine W arch arch arch) (safe : GridNativeDispatch.WordRoom I.D)
    (z : I.D.trace) (x : GridDiagonal.Pins (Fin rails)) (c : Cell (m+1) (l).sideMinusOne) (j : Fin v.copies),
    let table:=GridNativeDispatch.actualTable I.D safe
    let room:=GridNativeDispatch.selectorRoom I.D l R.table R.selector safe
    let sel:=InputWindow I.D l z safe room
    let t:=GridTicks.index (c,j)
    let rooms:=(R.rooms recv 0 gate).choose
    let widths:=fun i=>(v.replacement.width_le_size i).trans v.size_le
    let input:=streamInput I recv 0 gate R.text rooms widths table.codes room z x c j
    let start:=shifted l w input
    (GridReceiverDirectory.prefixProgram I.D l).Spec (·=start)
      (fun _=>Elected I.D l geom safe z sel t start (original I.D l sel input)) (prefixTime I.D l)

/-- The scheduled local-wire layout uses exactly the header, fixed tape bits,
registered assignment and root order used by the selected grid setting. -/
def streamLayout (geom : ElectionRoom I.D l) (recv : Machine W arch arch arch)
    (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace) :
    FactorPinIntervals.Layout (Cell (m+1) (l).sideMinusOne × Fin v.copies)
      I.inputSize (I.D.roots z.1) (l).pinWidth :=
  let room:=GridNativeDispatch.selectorRoom I.D l R.table R.selector safe
  let sel:=InputWindow I.D l z safe room
  let par:=GridNativeDispatch.params I.D l 0 gate
  let hd:=GridRegisteredPublication.headers (m:=m) (n:=(l).sideMinusOne) (q:=v.copies) I.D par recv sel R.text
  let adv:=GridPinCapturedSources.advice (S:=I.inputSize) (e:=rails) (compact:=(l).bank) v.replacement
    (FieldCode.ofCardLe I.D.field) par recv I.D.machine
  let model:=(R.rooms recv 0 gate).choose sel z
  let unit:=I.D.issuedUnit w degree stageRate rootRate
  FactorPinIntervals.scheduledLayout geom.teams_pos w
    (I.D.costs (GridNativeImage.resources I.D l) z.1 m (l).sideMinusOne (l).bank I.D.issuedCharges unit)
    (I.D.origin z.1) hd adv (I.D.pin_room (GridNativeImage.resources I.D l) z.1 I.D.issuedCharges unit hd model)

/-- These four projections give the semantics of the actual receiver's S5 scan. -/
theorem streamLayout_rows (geom : ElectionRoom I.D l) (recv : Machine W arch arch arch)
    (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace) :
    let P:=GridReceiverBanks.pinPlan I.D l
    let L:=streamLayout I R geom recv safe z
    let cost:=I.D.costs (GridNativeImage.resources I.D l) z.1 m (l).sideMinusOne (l).bank I.D.issuedCharges
      (I.D.issuedUnit w degree stageRate rootRate)
    (∀ i,L.origin i=I.D.origin z.1 i) ∧
      (∀ f,GridTicks.index (L.owner f)=FactorAllocation.owner geom.teams_pos w cost f) ∧
      (∀ t,L.rows t=FactorAllocation.factors w cost (List.finRange (I.D.roots z.1)) (GridTicks.index t)) ∧
      (∀ t,(L.header t).length=P.headerSize) := by
  intro P L cost
  refine ⟨fun _=>rfl,fun f=>GridTicks.index.apply_symm_apply _,fun _=>rfl,?_⟩
  intro t
  apply GridReceiverHeader.length

include R in
/-- All four input arrays and all computed interval offsets fit the very same
canonical publication plan on the independently recovered receiver root count. -/
theorem streamLayout_room (geom : ElectionRoom I.D l) (z : I.D.trace) :
    let P:=GridReceiverBanks.pinPlan I.D l
    let full:=2^(I.axes+1)
    let K:=(20*(w+1)+2)^((m+1)+2)
    let stages:=(GridReceiverDirectory.native I.D l).stages.length
    GridPinArena.Scalars W P I.inputSize full K (GridPinArena.slab w) ∧
      GridPinArena.Small w P I.inputSize full (stages*full) K := by
  intro P full K stages
  let N:=(GridReceiverDirectory.parameters I.D l).roots
  let src:=(GridNativeImage.resources I.D l).roots
  let d:=(I.axes+1)+w/2
  let base:=GridScale.external (m+1) (overhead Q loss w) (l).bank*2+SelfAdvice.textSize W arch arch
  let fuel:=2^(evalDepth w (m+1) A 2 (overhead Q loss w) v.copies)
  let G:=TraceStaticRow.gateTable I.D.field I.D.fit.width I.D.fit.labels base fuel I.D.state arch arch d
  have fromE : I.D.roots z.1=src := GridRegisteredOrder.roots_archive I.D w (1+(d+d)) G.cells
    (l).selectorCap (rails*2+w^2+(l).bank*w^2) z.1
  have same : src=N := fromE.symm.trans (GridReceiverDirectory.roots I.D l z.1)
  let mk:=fun a=>GridPinPublisher.canonical w (m+1) (l).sideMinusOne v.copies (l).pinWidth
    (GridNativeImage.parameterCount I.D l) ((l).selectorCap+1) (l).receiverText (l).bank rails
    I.inputSize a stages full (2*2^(w/2))
  have captured : GridPinArena.Small w (mk src) I.inputSize full (stages*full) K := R.fits.small
  have room : GridPinArena.Small w P I.inputSize full (stages*full) K := by
    change GridPinArena.Small w (mk N) I.inputSize full (stages*full) K
    exact same ▸ captured
  exact ⟨GridPinArena.canonical_scalars w (m+1) (l).sideMinusOne v.copies (l).pinWidth
    (GridNativeImage.parameterCount I.D l) ((l).selectorCap+1) (l).receiverText (l).bank rails
    I.inputSize N stages full (2*2^(w/2)) geom.pos room R.fits.actualSize.symm.le R.text,room⟩

/-- Through the actual tick filter, the original shifted pins remain resident
at their true incoming addresses. This includes all bytes of the selected header. -/
theorem elected_pins (geom : ElectionRoom I.D l) (safe : GridNativeDispatch.WordRoom I.D)
    (z : I.D.trace) (sel : Fin ((l).selectorCap+1)→Bool) (t : Fin (((l).sideMinusOne+1)^(m+1)*v.copies))
    {input origin out : Memory W} (got : Elected I.D l geom safe z sel t input origin out) :
    ∀ i<2+(l).pinWidth,out i=input i := by
  rcases got with ⟨r,history,c,cls,selected⟩
  rcases history with ⟨_,_,_,_,_,_,_,_,_,_,_,keep,_⟩
  have bits : (l).pinWidth≤2^w := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  let vAge:=receiverAge w
  let s:=TickWorkspace.stride vAge
  have ws : (2:ℕ)^w≤ s := by
    change 2^w≤(2^(vAge^10))^4
    rw [←pow_mul];have charge:=receiverAge_lower w
    exact Nat.pow_le_pow_right (by decide) (show w≤vAge^10*4 by dsimp only [vAge];omega)
  have low : (2:ℕ)^w≤GridDescription.sector w := Nat.pow_le_pow_right (by decide) (by omega : w≤32*w)
  have pos:=Nat.two_pow_pos w
  intro i hi
  rw [GridReceiverTickDirectory.outside_receiver geom.teams_pos _ t cls selected i (by omega)
    (.inl (show i<18*s by omega)) (.inl (show i<19*s by omega))]
  exact keep i (show i<21*s by omega)

end PerStream

set_option maxHeartbeats 1600000 in
/-- The native positive prefix is valid simultaneously on all selected
histories, cells, true external pins and multiplicity indices of the installed grid. -/
theorem eventual_installed_prefix (blk : Block F) (env : Envelopes Q loss) (m A degree stageRate rootRate : ℕ)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop,∀ (v : TickSelection F (m+1) A w Q loss), v.copies=q w →
      ∀ (I : Installed blk m A w degree stageRate rootRate v) {tariff power : ℕ}
        (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I tariff power),
        ∃ geom,InstalledPrefix I R geom := by
  let rate:=GridInstalledSmall.coefficient blk degree stageRate rootRate
  let scale:=trace_scale env (m+1) A 2 q range
  filter_upwards [GridReceiverDirectory.selected_prefix blk scale rate 2,
    eventual_election_room blk env m A degree stageRate rootRate q range,eventually_ge_atTop (64^10+1024)]
    with w physical geometry large
  intro v chosen I tariff power R
  let l:=layout m A w (overhead Q loss w) v.copies degree stageRate rootRate
  let geom:=geometry v chosen I
  refine ⟨geom,?_⟩
  intro recv safe z x c j
  let ct:=GridNativeDispatch.actualTable I.D safe
  let room:=GridNativeDispatch.selectorRoom I.D l R.table R.selector safe
  let sel:=InputWindow I.D l z safe room
  let t:=GridTicks.index (c,j)
  let gb:=26*GridDescription.sector w
  let rooms:=(R.rooms recv 0 gb).choose
  let ext:=fun i=>(v.replacement.width_le_size i).trans v.size_le
  let input:=streamInput I recv 0 gb R.text rooms ext ct.codes room z x c j
  let code:=GridDescription.code (q:=w^2) recv I.D.machine
  let head:=GridRegisteredPublication.headers (m:=m) (n:=l.sideMinusOne) (q:=v.copies) I.D (GridNativeDispatch.params I.D l 0 gb) recv sel R.text (c,j)
  have read : head.length≤l.pinWidth ∧ ∀ i:Fin head.length,input i.val=head[i.val] :=
    stream_header I recv 0 gb R.text rooms ext ct.codes room z x c j
  have text := stream_authentic I recv 0 gb R.text rooms ext ct.codes room (by omega) z x c j
  have bytes : SelfAdvice.textSize (64*w) (GridDescription.capacity w) (GridDescription.capacity w)≤head.length := by
    dsimp only [head,GridRegisteredPublication.headers]
    rw [GridReceiverHeader.length]
    exact Nat.le_add_right _ _
  have bits : l.pinWidth≤2^w := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have ws : (2:ℕ)^w≤TickWorkspace.stride (receiverAge w) := by
    change 2^w≤(2^((receiverAge w)^10))^4
    rw [←pow_mul]
    have charge:=receiverAge_lower w
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have double : 4*(2:ℕ)^w<2^(64*w) := by
    change 2^2*2^w<2^(64*w)
    rw [←pow_add];exact Nat.pow_lt_pow_right (by decide) (by omega)
  have pos := Nat.two_pow_pos w
  have pinSpace : 2+l.pinWidth+l.pinWidth<2^(64*w) := by omega
  have headLow : 2+head.length≤(GridReceiverDirectory.archive I.D l).seed := by
    change 2+head.length ≤ 21*TickWorkspace.stride (receiverAge w)
    have bound:=read.1
    omega
  have cpu : GridDescription.capacity w≤64*w := (Nat.div_le_self w 1024).trans (by omega)
  dsimp only at physical
  rw [←chosen,←I.block_eq,←I.passes_eq] at physical
  apply physical I.D.axesFit I.axes_eq cpu cpu cpu I.D.machine I.D.fit I.D.field I.D.state I.D.passesFit
    l geom safe z room t recv R.text code input
  · exact ⟨R.fits.degree,R.fits.setup,R.fits.maps⟩
  · exact R.fits.axes
  · exact (rooms sel z).external
  · exact R.fits.cut
  · exact bytes.trans read.1
  · exact text
  · exact pinSpace
  · exact read.1
  · exact headLow
  · exact read.2

end Hierarchy.GridChosenReceiver
end

end OAI
