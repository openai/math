import OAI.Hierarchy.DescentSavedRotationNamed
import OAI.Hierarchy.DescentRecordedStencilCell
import OAI.Hierarchy.DescentResetPortTotal
import OAI.Hierarchy.DescentResetIssuedWords

namespace OAI
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentGLPacked.BankImage DescentGLPacked.BankImage.Dated ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

open DescentIssuedFallbackPanel DescentGLPacked DescentPlainTerminal DescentPlainTerminal.Suffix DescentPackedZip
open DescentPackedFlowPair.Padded DescentPacking.PackedMatch.Local
namespace ClosedReset.Recorded
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (E : EstimatorArena)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "owners" => Fintype.card input.V
local notation "full" => (A).wire*((A).z*G.b)*(A).cap


local notation "HP" => S.hostSize i
local notation "cc" => reset.terminals.commonDepth
local notation:max "xy" eqn:arg => (Equiv.cast (congrArg Block ((eqn).trans reset.keyWidth))).trans sourceDigits
local notation:max "hostIDs" eqn:arg => ((A).numberedHeader (xy eqn) input.vertex).site
local notation:max "savedAt" fresh:arg => fresh+(2^E.dim)^E.dim+(2^E.dim)^E.dim
local notation:max "firstAt" fresh:arg => (savedAt fresh)+1
local notation "originalWidth" => S.groupWidth k tail i+k

def stencilSources (count hub roster : Bank) : StencilBook.Sources:=
  ⟨.lookup count (.lit 0),E.depthRows,hub,firstContactBank E,roster,E.precision⟩

def stencilLayout (maxPorts batch nbits tbits : ℕ) :=
  PackedFlow.Padded.stencilBook A HP cc E.dim maxPorts E.high batch E.precision nbits tbits
    (Nat.clog 2 (E.dim+2)) (E.dim+S.censusBits p)

include accepted in
private theorem depth_agrees {m : ℕ} (eqn : m=originalWidth) (v:input.V) :
    let digits:=(Equiv.cast (congrArg Block eqn)).trans sourceDigits
    let name:=((A).numberedHeader digits input.vertex).site
    ((A).mixerHeader digits name).depth A f v=reset.reset.placement.b (reset.frame.host v) := by
  subst m
  exact (accepted.measured.depth v).symm

local notation:max "workbook" maxPorts:arg batch:arg nbits:arg tbits:arg => stencilLayout (reset:=reset) (p:=p) E maxPorts batch nbits tbits
local notation:max "remixed" C':arg => (((C').chosen E.dim).bank (DescentGLNielsen.schedule E.dim).length)
local notation:max "lastOut" first:arg maxPorts:arg ratio:arg batch:arg => Subwords.destination first (E.precision*2^(E.dim-cc))
  (((1+maxPorts)+E.dim)*HP) (2^cc) ratio batch
local notation:max "lastBase" first:arg maxPorts:arg ratio:arg batch:arg => Subwords.finish first (E.precision*2^(E.dim-cc))
  (((1+maxPorts)+E.dim)*HP) (2^cc) ratio batch

/-- The same native memory contains the original padded Walsh zero coefficients and
all occupied attained-depth rows after the stencil passes. -/
def StencilReservationWords {w : ℕ} (dim : E.dim=reset.reset.k) (maxPorts : ℕ)
    (ports : D≤ maxPorts) (mem : Memory w) : Prop :=
  ∃(hh : E.hosts=S.hostSize i*(E.dim+1+maxPorts)),
    E.FirstTotals (publicLoad E dim maxPorts ports hh) mem ∧
      ∀v,mem (E.depthRows.base+(input.vertex v).val*(E.dim+1))=
        (((A).numberedHeader sourceDigits input.vertex).depth A f v:Word w)

include accepted in
theorem issued_stencil_reserved {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (siteBase peerBase pitch keep : ℕ) (width : S.hostSize i*2^E.high≤pitch)
    (siteEnd : siteBase+S.hostSize i*2^E.high≤E.start) (peerEnd : peerBase+maxPorts*pitch≤E.start)
    (siteSave : siteBase+S.hostSize i*2^E.high≤E.origin ∨ E.staticEnd≤ siteBase)
    (peerSave : peerBase+maxPorts*pitch≤E.origin ∨ E.staticEnd≤peerBase)
    (primed :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      ∃prior : Memory w,prepare.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
          E.depthRows.base E.gainRows.base E.start prior ∧
        PackedFlow.Canvas.Originals («HP»:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
          A name digits siteBase peerBase pitch prior ∧ ∀x<keep,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank)
    (C' : Chart) (origin bitSites bitPeers : ℕ) (pcap : 0<E.precision)
    (base : E.endAddress≤origin)
    (siteFit : (⟨siteBase,bitSites⟩:Bank).Fits w origin)
    (pairFit : ∀j : Fin maxPorts,(⟨peerBase+j.val*pitch,bitPeers⟩:Bank).Fits w origin)
    (rows : S.hostSize i*2^E.high≤2^bitSites) (paidRows : S.hostSize i*2^E.high≤2^bitPeers)
    (area : Size C' (((1+maxPorts)+E.dim)*S.hostSize i) E.high E.low E.precision w)
    (endWords : wordEnd origin E.high E.low≤C'.input.base) (gap : C'.input.base+C'.input.size≤C'.flags)
    (scaleWords : (powers origin E.dim).Fits w C'.input.base)
    (addresses : (cols origin E.dim).offsets.Fits w C'.input.base)
    (switches : (cols origin E.dim).switches.Fits w C'.input.base)
    (planes : ∀j : Fin E.dim,(Original.bank (plane origin E.dim) E.high j).Fits w C'.input.base)
    (fresh : ℕ) (ptrLow : ∀a : Fin E.dim,PhysicalTrajectory.pointer E.dim E.solveAt a.val < fresh)
    (space : fresh+(2^E.dim)^E.dim+(2^E.dim)^E.dim+1 < 2^w)
    (count hub roster : Bank) (low : ℕ) (oldCells : low≤ min keep E.start) (beforeTables : low≤E.origin)
    (beforeSave : E.endAddress≤fresh) (oldCount : count.Fits w low) (oldHubs : hub.Fits w low)
    (oldRoster : roster.Fits w low) (hubsRoom : HP≤hub.size) (rosterRoom : HP*(A).degree≤roster.size)
    (counted : mem count.base=(owners:Word w)) (hubWord : ∀v,mem (hub.base+((hostIDs dim) v).val)=(((A).hub v).toNat:Word w))
    (neighbors : ∀v j,mem (roster.base+(v.val*(A).degree+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster (D:=(A).degree) A (hostIDs dim) input.valid.host v j):Word w))
    (stored : (remixed C').Fits w fresh) (stores : ((1+maxPorts)+E.dim)*HP*2^E.high≤(remixed C').size)
    (spectra : (firstContactBank E).Fits w (firstAt fresh)) (depthFit : E.depthRows.Fits w (firstAt fresh))
    (ratio batch K₀ nbits tbits : ℕ) (lanes : ratio*batch*2^(E.dim-cc)=2^E.low)
    (factor : 2^cc=K₀*(ratio*batch)) (ratioPos : 0<ratio) (batchPos : 0<batch)
    (afterAddr : (workbook maxPorts batch nbits tbits).endAddress (lastBase (firstAt fresh) maxPorts ratio batch)<2^w)
    (laneBits : batch*max (nbits*Stencil.count (E.dim-cc) ((A).degree+(A).degree)) (tbits*2^(E.dim-cc))≤w/2)
    (cellBits : nbits*batch≤w) (capBits : 2^(E.dim-cc)*full<2^nbits)
    (levelBits : E.dim-cc<2^nbits) (one : 1<2^nbits)
    (headerBits : Nat.clog 2 (E.dim+2)+(E.dim+S.censusBits p)≤w)
    (hostBits : HP<2^w) (roomCode : 2*DescentFallbackShapeTable.rows (E.dim-cc) (2^reset.reset.n)≤2^tbits)
    (positiveD : 0<32*Nat.clog 2 (2*(A).degree)) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let name := ((A).numberedHeader digits input.vertex).site
    let ps := fun j : Fin maxPorts=>(⟨peerBase+j.val*pitch,bitPeers⟩:Bank)
    let sites : Bank:=⟨siteBase,bitSites⟩
    let H:=S.hostSize i
    let nG:=((1+maxPorts)+E.dim)*H
    let tables:=controlImage (h:=E.high) (l:=E.low) (w:=w) origin pcap
    let route:=routes C' nG E.high E.low E.precision w
    let move:=gathered C' origin E.solveAt sites ps H E.high E.low w
    let fee:=gatherFee C' origin E.solveAt sites ps H E.high E.low
    let previous:=prepare.seq ((E.header (w:=w)).program.seq (E.cpu w))
    let suffix:=(tables.program.seq route.program).seq move
    let ptr:=fun a : Fin E.dim=>PhysicalTrajectory.pointer E.dim E.solveAt a.val
    let n:=(2^E.dim)^E.dim
    let I:=DescentExteriorRotationWord.resetSheet E.dim w fresh
    let off : Bank:=⟨fresh,E.dim*E.dim⟩
    let table : Bank:=⟨fresh+n,E.dim*E.dim⟩
    let out:=fresh+n+n
    let op:=DescentExteriorRotationWord.reset off table ptr
    let save:=I.program.seq (scan w out 1 op)
    let chart:=workbook maxPorts batch nbits tbits
    let X:=stencilSources E count hub roster
    let floor:=out+1
    let dest:=lastOut floor maxPorts ratio batch
    let bank:=lastBase floor maxPorts ratio batch
    let sub:=PackedFlow.Padded.repackProgram chart (remixed C') floor ratio factor ratioPos batchPos w
    let cost:=PackedFlow.Padded.repackTime chart (remixed C') floor ratio factor ratioPos batchPos
    let cpu:=sub.seq (PackedFlow.Padded.paidProgram chart X bank dest f full K g full (2^reset.reset.n) w)
    let tick:=cost+PackedFlow.Padded.paidTime chart X bank dest f full g
    ∃(μ : Layout E.dim) (dst : Memory w),HEq μ reset.frame.basis ∧
      (previous.seq ((suffix.seq save).seq cpu)).Exec mem dst
        ((t+(4+10*(E.staticEnd-E.origin)+E.clock))+
         ((((8+10*(tables.length+route.length))+fee)+((4+10*(n+n))+(20+24*E.dim)))+tick)) ∧
      (((previous.seq suffix).seq save).seq cpu).Exec mem dst
        ((((t+(4+10*(E.staticEnd-E.origin)+E.clock))+((8+10*(tables.length+route.length))+fee))+
          ((4+10*(n+n))+(20+24*E.dim)))+tick) ∧
      dst out=((DescentExterior.matrixCode μ).val:Word w) ∧
      (∀a<low,dst a=mem a) ∧
      StencilReservationWords (reset:=reset) E dim maxPorts ports dst ∧
      chart.OldOrder X bank dest g cc μ dst ∧
      PackedFlow.Padded.Published (h:=E.high) (l:=E.low) batch tbits (chart.output bank)
        (name.toEmbedding.trans (Fin.castLEEmb input.valid.host))
        (fun v hi x=>(2*Stencil.shapeCode (E.dim-cc) (2^reset.reset.n)
          (fieldsRelative cc (originalCell (reset:=reset) v ((rearrange reset.frame.basis).symm
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) (dim.trans reset.keyWidth)) x)))))+
          (((A).hub v) || decide ((reset.frame.host v,group (reset.reset.placement.b (reset.frame.host v))
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) (dim.trans reset.keyWidth)) x)))∈reset.reset.placement.keys)).toNat:ℕ)) dst := by
  intro digits name ps sites HH nG tables route move fee previous suffix ptr nn I off look out op save chart X floor dest bank sub cost cpu tick
  obtain ⟨prior,μ,mid,saved,eqn,earlier,_,matrix,protect,denseRead,_,older,sourceRun,middleRun,_,retain,totals,_smoothed,hasDepth⟩:=
    accepted.saved_rotation_parts E dim mem prepare t maxPorts ports hostCount siteBase peerBase pitch keep width siteEnd peerEnd
    siteSave peerSave primed grain old branch live localBits localGain fit stage small score endRoom issue C' origin bitSites bitPeers
    pcap base siteFit pairFit rows paidRows area endWords gap scaleWords addresses switches planes fresh ptrLow space
  have oldBefore:low≤fresh:=by
    have start:E.start≤E.endAddress:=by rw [E.endAddress_eq];omega
    exact ((oldCells.trans (min_le_right ..)).trans start).trans beforeSave
  have keepLow (a:ℕ) (ha:a<low):saved a=mem a:=older a (ha.trans_le oldCells) (.inl (ha.trans_le beforeTables)) (ha.trans_le oldBefore)
  have begin:fresh≤floor:=by change fresh≤fresh+nn+nn+1;omega
  have bprior : StencilBook.Sources.Before X w floor:=by
    have lift {T:Bank} (h:T.Fits w low) : T.Fits w floor:=⟨h.1,h.2.1,h.2.2.trans (oldBefore.trans begin)⟩
    exact ⟨⟨lift oldCount,trivial⟩,depthFit,lift oldHubs,spectra,lift oldRoster⟩
  have dense ch : DescentGLPacked.Dense (h:=E.high) (l:=E.low) (slice (remixed C').base HP (2^E.high) ch)
      (fun v x=>PackedFlow.Channels.values (fun (v:Fin HP) a=>(PackedFlow.Padded.load A name digits v a:Cell E.precision))
        (fun (j:Fin maxPorts) (v:Fin HP) a=>(PackedFlow.Padded.flow A name digits j v a:Cell E.precision))
        pcap ch v ((rearrange μ).symm x)) saved:=by
    intro u
    have rr:=(DescentSIMDLookup.row HP (2^E.dim) (2^E.low) u).isLt
    change _ < HP * chunks (2^(E.high+E.low)) (2^E.low) at rr
    rw [DescentGLPacked.chunk_count] at rr
    have room:=Nat.mul_le_mul_right (HP*2^E.high) ch.isLt
    rw [Nat.succ_mul] at room
    have fits:=stored.2.2
    have addr:slice (remixed C').base HP (2^E.high) ch+(DescentSIMDLookup.row HP (2^E.dim) (2^E.low) u).val<fresh:=by
      have stack : (1+maxPorts+(E.high+E.low))*(HP*2^E.high) ≤ (remixed C').size := by
        rw [←Nat.mul_assoc]
        exact stores
      change (remixed C').base + ch.val * HP * 2^E.high + _ < fresh
      rw [Nat.mul_assoc]
      omega
    exact (protect _ (.inl addr)).trans (denseRead ch u)
  let depth:=((A).mixerHeader digits name).depth A f
  have lower (v:input.V) : cc≤depth v ∧ depth v≤E.dim:=by
    have agree : depth v = reset.reset.placement.b (reset.frame.host v) :=
      accepted.depth_agrees (dim.trans reset.keyWidth) v
    rw [agree]
    exact ⟨reset.terminals.commonLow _,(reset.reset.placement.depth _).trans_eq dim.symm⟩
  have ceiling:full<2^(S.censusBits p):=
    ((A).census_caps_at S input.valid ctl.height reset.age.le (input.grain.trans grain) (input.edges.trans old) branch).2
  have precision:S.censusBits p≤E.precision:=by rw [localBits];unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have shortV:=ceiling.trans_le (Nat.pow_le_pow_right (by decide) precision)
  have cobound:∀v x,(A).resetLoad digits v x<2^E.precision := fun v x=>
    ((A).reset_words_at S input.valid digits v v x).2.trans_lt shortV
  have oneLoad:∀(v:Fin HP) x,PackedFlow.Padded.load A name digits v x<2^E.precision:=by
    intro v x;unfold PackedFlow.Padded.load
    cases project ((A).numberedHeader digits input.vertex).sites v
    · exact Nat.two_pow_pos _
    · exact cobound _ _
  have oneFlow:∀(j:Fin maxPorts) (v:Fin HP) x,PackedFlow.Padded.flow A name digits j v x<2^E.precision:=by
    intro j v x;unfold PackedFlow.Padded.flow
    cases project ((A).numberedHeader digits input.vertex).sites v with
    | none=>exact Nat.two_pow_pos _
    | some vv=>
      cases project (A).degree j with
      | none=>exact Nat.two_pow_pos _
      | some jj=>
        simp only [Option.elim_some]
        unfold PackedFlow.raw
        cases PackedFlow.next A name vv jj with
        | none=>exact Nat.two_pow_pos _
        | some u=>exact ((A).reset_words_at S input.valid digits (name.symm vv) (name.symm u) x).1.trans_lt (cobound _ _)
  have totalFit (v u) : (∑x,(A).resetFlow digits v u x)<2^(E.dim+S.censusBits p):=
    Cutoff.total_fits _ (fun x=>((A).reset_words_at S input.valid digits v u x).1.trans_lt
      (((A).reset_words_at S input.valid digits v u x).2.trans_lt ceiling))
  have totalOn:=E.retained_totals (E.image (E.literal prior)) saved _ (le_min base beforeSave) retain totals
  have dep (v:input.V) : saved (E.depthRows.base+(name v).val*(E.dim+1))=(depth v:Word w):=by
    apply hasDepth v
    exact (depth_before_end E fit (name v).val HP maxPorts ((name v).isLt.trans_le input.valid.host) hostCount).trans_le
      (le_min base beforeSave)
  have levRows:HP*(E.dim+1)≤E.depthRows.size:=by
    apply le_trans _ fit.hostRows.1
    rw [hostCount]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right ..)
  have spectrumRows:HP*(E.dim+1+maxPorts)*2^E.high≤(firstContactBank E).size:=by
    rw [←hostCount];exact Nat.le_pow_clog (by decide) _
  have top:E.dim<2^(Nat.clog 2 (E.dim+2)):= (by omega : E.dim<E.dim+2).trans_le (Nat.le_pow_clog (by decide) _)
  have smallCut:cc≤E.dim:=by rw [dim,reset.frame.extent];exact reset.frame.enough.trans (Nat.sub_le ..)
  have rawCount p₀ : X.count.eval saved ((DescentSIMDLookup.row HP (2^cc) batch p₀).val:Word w)=(owners:Word w):=by
    change count.read saved ((0:ℕ):Word w)=_
    exact (bank_read count saved (i:=0) oldCount.1 oldCount).trans
      ((keepLow count.base (by have := oldCount.1; have := oldCount.2.2; omega)).trans counted)
  have realHubs v:saved (hub.base+(name v).val)=(((A).hub v).toNat:Word w):=
    (keepLow _ ((Nat.add_lt_add_left (((name v).isLt.trans_le input.valid.host).trans_le hubsRoom) _).trans_le oldHubs.2.2)).trans (hubWord v)
  have realPeers v j:saved (roster.base+(v.val*(A).degree+j.val))=(DescentPackedColony.target
      (PackedFlow.Padded.roster (D:=(A).degree) A name input.valid.host v j):Word w):=by
    have lim:=Nat.mul_le_mul_right (A).degree v.isLt;rw [Nat.succ_mul] at lim
    exact (keepLow _ (by have :=oldRoster.2.2;have :=j.isLt;omega)).trans (neighbors v j)
  have head:chart.afterHeader bank<2^w:=by
    let readers := chart.readers bank
    let last := chart.last bank
    have a : chart.afterHeader bank ≤ readers.first := Nat.le_add_right ..
    have b : readers.first ≤ readers.planeBase := Nat.le_add_right ..
    have c : readers.planeBase ≤ readers.stop := Nat.le_add_right ..
    have d : readers.stop ≤ last.table := Nat.le_add_right ..
    have e : last.table ≤ last.mask := Nat.le_add_right ..
    have f : last.mask ≤ last.scratch := Nat.le_add_right ..
    have g : last.scratch ≤ last.out := Nat.le_add_right ..
    have h : last.out ≤ chart.endAddress bank := Nat.le_add_right ..
    exact (a.trans (b.trans (c.trans (d.trans (e.trans (f.trans (g.trans h))))))).trans_lt afterAddr
  have solve:=PackedFlow.Padded.run_from_remix (h:=E.high) (l:=E.low) A name digits floor ratio smallCut input.valid.host
    (input.branch.le.trans ports) μ f full K g full (2^reset.reset.n) depth X (remixed C') K₀ saved lanes factor ratioPos
    pcap batchPos afterAddr laneBits cellBits bprior ⟨stored.1,stored.2.1,stored.2.2.trans begin⟩ stores rosterRoom
    head hostBits levelBits one capBits levRows hubsRoom spectrumRows (by change E.precision ≤ w; omega) headerBits top lower totalFit oneLoad oneFlow
    rawCount realHubs dep (paid_total E dim maxPorts ports hostCount saved totalOn) realPeers dense
  obtain ⟨dst,ran,_digit,preserve,ordered,allWords⟩:=solve
  refine ⟨μ,dst,eqn,sourceRun.then (middleRun.then ran),earlier.then ran,(preserve _ (.inl (by change out<out+1;omega))).trans matrix,
    fun a ha=>(preserve a (.inl (ha.trans_le (oldBefore.trans begin)))).trans (keepLow a ha),?_,ordered,?_⟩
  · refine ⟨hostCount,E.retained_totals saved dst _ (beforeSave.trans begin) (fun z hz=>preserve _ (.inl hz)) totalOn,?_⟩
    intro v
    have limit:=(depth_before_end E fit (name v).val HP maxPorts ((name v).isLt.trans_le input.valid.host) hostCount).trans_le (beforeSave.trans begin)
    change dst (E.depthRows.base+(name v).val*(E.dim+1)) = _
    refine (preserve _ (.inl limit)).trans ((dep v).trans ?_)
    apply congrArg (fun n : ℕ => (n : Word w))
    exact (accepted.depth_agrees (dim.trans reset.keyWidth) v).trans (accepted.measured.depth v)

  · obtain ⟨values,actual,atReal⟩:=allWords
    refine ⟨values,actual,?_⟩
    intro v hi x
    refine (atReal v hi x).trans ?_
    let panel := realPanel (reset:=reset) (dim.trans reset.keyWidth) μ nbits tbits v hi x
    change panel = _
    apply Fin.ext
    have oldCell := accepted.stencil_cell (dim.trans reset.keyWidth) μ eqn levelBits one capBits roomCode
      live (by unfold quota;omega) positiveD v hi x
    simp only [Equiv.apply_symm_apply] at oldCell
    exact oldCell.trans (Fin.val_cast_of_lt (oldCell ▸ panel.isLt)).symm


include accepted in
theorem issued_stencil {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (siteBase peerBase pitch keep : ℕ) (width : S.hostSize i*2^E.high≤pitch)
    (siteEnd : siteBase+S.hostSize i*2^E.high≤E.start) (peerEnd : peerBase+maxPorts*pitch≤E.start)
    (siteSave : siteBase+S.hostSize i*2^E.high≤E.origin ∨ E.staticEnd≤ siteBase)
    (peerSave : peerBase+maxPorts*pitch≤E.origin ∨ E.staticEnd≤peerBase)
    (primed :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      ∃prior : Memory w,prepare.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
          E.depthRows.base E.gainRows.base E.start prior ∧
        PackedFlow.Canvas.Originals («HP»:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
          A name digits siteBase peerBase pitch prior ∧ ∀x<keep,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank)
    (C' : Chart) (origin bitSites bitPeers : ℕ) (pcap : 0<E.precision)
    (base : E.endAddress≤origin)
    (siteFit : (⟨siteBase,bitSites⟩:Bank).Fits w origin)
    (pairFit : ∀j : Fin maxPorts,(⟨peerBase+j.val*pitch,bitPeers⟩:Bank).Fits w origin)
    (rows : S.hostSize i*2^E.high≤2^bitSites) (paidRows : S.hostSize i*2^E.high≤2^bitPeers)
    (area : Size C' (((1+maxPorts)+E.dim)*S.hostSize i) E.high E.low E.precision w)
    (endWords : wordEnd origin E.high E.low≤C'.input.base) (gap : C'.input.base+C'.input.size≤C'.flags)
    (scaleWords : (powers origin E.dim).Fits w C'.input.base)
    (addresses : (cols origin E.dim).offsets.Fits w C'.input.base)
    (switches : (cols origin E.dim).switches.Fits w C'.input.base)
    (planes : ∀j : Fin E.dim,(Original.bank (plane origin E.dim) E.high j).Fits w C'.input.base)
    (fresh : ℕ) (ptrLow : ∀a : Fin E.dim,PhysicalTrajectory.pointer E.dim E.solveAt a.val < fresh)
    (space : fresh+(2^E.dim)^E.dim+(2^E.dim)^E.dim+1 < 2^w)
    (count hub roster : Bank) (low : ℕ) (oldCells : low≤ min keep E.start) (beforeTables : low≤E.origin)
    (beforeSave : E.endAddress≤fresh) (oldCount : count.Fits w low) (oldHubs : hub.Fits w low)
    (oldRoster : roster.Fits w low) (hubsRoom : HP≤hub.size) (rosterRoom : HP*(A).degree≤roster.size)
    (counted : mem count.base=(owners:Word w)) (hubWord : ∀v,mem (hub.base+((hostIDs dim) v).val)=(((A).hub v).toNat:Word w))
    (neighbors : ∀v j,mem (roster.base+(v.val*(A).degree+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster (D:=(A).degree) A (hostIDs dim) input.valid.host v j):Word w))
    (stored : (remixed C').Fits w fresh) (stores : ((1+maxPorts)+E.dim)*HP*2^E.high≤(remixed C').size)
    (spectra : (firstContactBank E).Fits w (firstAt fresh)) (depthFit : E.depthRows.Fits w (firstAt fresh))
    (ratio batch K₀ nbits tbits : ℕ) (lanes : ratio*batch*2^(E.dim-cc)=2^E.low)
    (factor : 2^cc=K₀*(ratio*batch)) (ratioPos : 0<ratio) (batchPos : 0<batch)
    (afterAddr : (workbook maxPorts batch nbits tbits).endAddress (lastBase (firstAt fresh) maxPorts ratio batch)<2^w)
    (laneBits : batch*max (nbits*Stencil.count (E.dim-cc) ((A).degree+(A).degree)) (tbits*2^(E.dim-cc))≤w/2)
    (cellBits : nbits*batch≤w) (capBits : 2^(E.dim-cc)*full<2^nbits)
    (levelBits : E.dim-cc<2^nbits) (one : 1<2^nbits)
    (headerBits : Nat.clog 2 (E.dim+2)+(E.dim+S.censusBits p)≤w)
    (hostBits : HP<2^w) (roomCode : 2*DescentFallbackShapeTable.rows (E.dim-cc) (2^reset.reset.n)≤2^tbits)
    (positiveD : 0<32*Nat.clog 2 (2*(A).degree)) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let name := ((A).numberedHeader digits input.vertex).site
    let ps := fun j : Fin maxPorts=>(⟨peerBase+j.val*pitch,bitPeers⟩:Bank)
    let sites : Bank:=⟨siteBase,bitSites⟩
    let H:=S.hostSize i
    let nG:=((1+maxPorts)+E.dim)*H
    let tables:=controlImage (h:=E.high) (l:=E.low) (w:=w) origin pcap
    let route:=routes C' nG E.high E.low E.precision w
    let move:=gathered C' origin E.solveAt sites ps H E.high E.low w
    let fee:=gatherFee C' origin E.solveAt sites ps H E.high E.low
    let previous:=prepare.seq ((E.header (w:=w)).program.seq (E.cpu w))
    let suffix:=(tables.program.seq route.program).seq move
    let ptr:=fun a : Fin E.dim=>PhysicalTrajectory.pointer E.dim E.solveAt a.val
    let n:=(2^E.dim)^E.dim
    let I:=DescentExteriorRotationWord.resetSheet E.dim w fresh
    let off : Bank:=⟨fresh,E.dim*E.dim⟩
    let table : Bank:=⟨fresh+n,E.dim*E.dim⟩
    let out:=fresh+n+n
    let op:=DescentExteriorRotationWord.reset off table ptr
    let save:=I.program.seq (scan w out 1 op)
    let chart:=workbook maxPorts batch nbits tbits
    let X:=stencilSources E count hub roster
    let floor:=out+1
    let dest:=lastOut floor maxPorts ratio batch
    let bank:=lastBase floor maxPorts ratio batch
    let sub:=PackedFlow.Padded.repackProgram chart (remixed C') floor ratio factor ratioPos batchPos w
    let cost:=PackedFlow.Padded.repackTime chart (remixed C') floor ratio factor ratioPos batchPos
    let cpu:=sub.seq (PackedFlow.Padded.paidProgram chart X bank dest f full K g full (2^reset.reset.n) w)
    let tick:=cost+PackedFlow.Padded.paidTime chart X bank dest f full g
    ∃(μ : Layout E.dim) (dst : Memory w),HEq μ reset.frame.basis ∧
      (previous.seq ((suffix.seq save).seq cpu)).Exec mem dst
        ((t+(4+10*(E.staticEnd-E.origin)+E.clock))+
         ((((8+10*(tables.length+route.length))+fee)+((4+10*(n+n))+(20+24*E.dim)))+tick)) ∧
      (((previous.seq suffix).seq save).seq cpu).Exec mem dst
        ((((t+(4+10*(E.staticEnd-E.origin)+E.clock))+((8+10*(tables.length+route.length))+fee))+
          ((4+10*(n+n))+(20+24*E.dim)))+tick) ∧
      dst out=((DescentExterior.matrixCode μ).val:Word w) ∧
      (∀a<low,dst a=mem a) ∧
      chart.OldOrder X bank dest g cc μ dst ∧
      PackedFlow.Padded.Published (h:=E.high) (l:=E.low) batch tbits (chart.output bank)
        (name.toEmbedding.trans (Fin.castLEEmb input.valid.host))
        (fun v hi x=>(2*Stencil.shapeCode (E.dim-cc) (2^reset.reset.n)
          (fieldsRelative cc (originalCell (reset:=reset) v ((rearrange reset.frame.basis).symm
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) (dim.trans reset.keyWidth)) x)))))+
          (((A).hub v) || decide ((reset.frame.host v,group (reset.reset.placement.b (reset.frame.host v))
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) (dim.trans reset.keyWidth)) x)))∈reset.reset.placement.keys)).toNat:ℕ)) dst := by
  intro digits name ps sites HH nG tables route move fee previous suffix ptr nn I off look out op save chart X floor dest bank sub cost cpu tick
  obtain ⟨μ,dst,coupled,seqRun,run,matrix,kept,_,order,words⟩:=
    accepted.issued_stencil_reserved E dim mem prepare t maxPorts ports hostCount siteBase peerBase pitch keep width siteEnd peerEnd siteSave peerSave primed grain old branch live localBits localGain fit stage small score endRoom issue C' origin bitSites bitPeers pcap base siteFit pairFit rows paidRows area endWords gap scaleWords addresses switches planes fresh ptrLow space count hub roster low oldCells beforeTables beforeSave oldCount oldHubs oldRoster hubsRoom rosterRoom counted hubWord neighbors stored stores spectra depthFit ratio batch K₀ nbits tbits lanes factor ratioPos batchPos afterAddr laneBits cellBits capBits levelBits one headerBits hostBits roomCode positiveD
  exact ⟨μ,dst,coupled,seqRun,run,matrix,kept,order,words⟩

end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
