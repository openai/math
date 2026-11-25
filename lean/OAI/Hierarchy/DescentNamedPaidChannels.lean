import OAI.Hierarchy.DescentResetPeerCorrectionRoom
import OAI.Hierarchy.DescentPriorFundedRegisters
import OAI.Hierarchy.DescentFundedPreviousBank
import OAI.Hierarchy.DescentNamedPaidMemory
import OAI.Hierarchy.DescentFundedInputTransport

namespace OAI
/-! # The original dated paid and signed channels on the attained prefix memory -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentCompiler DescentSixParty DescentSixParty.ClosedReset.Window DescentDenseHostOrder
open DescentFundedCensus DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentPackedZip
open DescentSixParty.ClosedReset DescentPackedColony
open DescentGL DescentPaidResidentCount.Reset DescentSharedCableNames DescentIssuedFallbackPanel DescentColonies
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k age z D n h C f g cut tail wire hist : ℕ}
    {ctl : ResetRates G S k D n h C f g cut tail} {prior : Reached W G q ε S k age z D wire hist}
    (B : ClosedReset prior ctl) {p : ℕ} (recorded : B.Recorded p)
    (drift maxDegree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
    (venue : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "A" => prior.placement
local notation "Z" => B.reset
local notation "dep" => GroupStage.depthBound D n f g
local notation "rel" => ((Z).k-B.terminals.commonDepth)
local notation "pool" => roster (Z).graph rel dep
local notation "a" => named G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "foot" => (a).stageStart floor
local notation "cens" => (a).successor.venue.census
local notation "fund" => (a).successor.funded
local notation "roots" => namedRoots G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor
local notation "atlas" => namedAtlas G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor
variable {w : ℕ} {u : (named G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR oldLanes primitiveLanes printedBits venue io.wire io.roster floor).DateInputs ((named G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR oldLanes primitiveLanes printedBits venue io.wire io.roster floor).stageStart floor) w} (run : u.FinalInputs)
local notation "phase" => (a).stencilPhase u.shape foot u.count u.hub u.g u.Y
local notation "flag" j:arg => presence («a»:=a) (floor:=foot) j
local notation "samePorts" => fundedPorts (funded_residual B) B.dimension run.ports


local notation "b₀" => (a).rebased foot
local notation "v₀" => (a).successor
local notation "base" => (v₀).fundedEnd b₀
local notation "start" => (v₀).finalEnd b₀
local notation "key" => (⟨(phase).saved,0⟩:Bank)
local notation "cc" => B.terminals.commonDepth
local notation "small₀" => (S.groupWidth k tail age+k-cc)
local notation "L" => 2^small₀
local notation "b" => (cens).bits
local notation "H" => venue.hosts
local notation "M₀" => 2^e
local notation "field" => u.roots.field
local notation "header" => (phase).S.t
local notation "sig" => DescentSignedCableCodec.width (A).degree (A).cap
local notation "mass" => (A).wire*((A).z*G.b)*(A).cap
local notation "block" => S.resetInputDigits ctl.base ctl.radix age
local notation "basis" => B.frame.basis
local notation "enough₀" => B.frame.enough.trans (Nat.sub_le ..)
local notation "oldIx" hi:arg lo:arg => (rearrange basis).symm (join enough₀ hi lo)
local notation "after" m:arg => (fund).memory start run.earlier key m
local notation "paidRAM" m:arg => DescentFundedCensus.memory run.jobs base (after m)
local notation "jCount" eg:arg => source_rows (p:=p) B drift maxDegree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor eg

local notation "c₀" => S.groupWidth k tail age
local notation "high" => c₀-e
local notation "low" => e+k
local notation "physical" => (⟨venue.hosts,S.groupCount age,2^k,venue.lanes,M₀,b,high,low,cc,(A).degree,(A).cap,M₀⟩:Setup)
local notation "phase₀" => (a).rootPhase u.shape foot u.count u.hub u.g u.Y u.roots w
local notation "signal" => (fun j:Fin (2*(fund).capacity)=>(Expr.lookup ((phase₀).tapped (j.cast (congrArg (2*·) run.signedCount))) .row))
private theorem split_sum {c e k : ℕ} (h : e≤c) : c-e+(e+k)=c+k:=by omega
local notation "ageDim" batch:arg => split_sum (k:=k) batch

theorem paid_channels
    (blocks : venue.k=k) (groups : venue.groups=S.groupCount age)
    (degree : venue.degree=D) (capacity : venue.cap=(A).cap)
    (oldRoom : Fintype.card prior.V≤H) (mem : Memory w) (safe : run.Room)
    (batch : e≤c₀) (oldPos : 0<venue.lanes)
    (μ : DescentGL.Layout (high+low)) (picked : HEq μ B.frame.basis)
    (saved : mem (key).base=((DescentExterior.matrixCode μ).val:Word w))
    (room : ∀x:Block k,H*chunks (S.groupCount age) venue.lanes≤(priorBank run.io x.val).size)
    (oldPaid : ∀x:Block k,Reads (priorBank run.io x.val) (fun v g=>Census.count A (Equiv.refl _)
      (prior.vertex.trans (Fin.castLEEmb oldRoom)) b v g x) venue.lanes mem)
    (incoming : Fin (2*(A).cap)→Fin H→Block cc→Fin L→Cell sig)
    (tapSpace : ∀j,(signal j).Fits w start)
    (taps : ∀j:Fin (2*(A).cap),Source (signal (j.cast (congrArg (2*·) capacity.symm)))
      (fun v hi=>encode sig (physical).donors (fun l=>incoming j v hi
        (Fin.cast (by change 2^(high+low-cc)=L;rw [ageDim batch]) l))) M₀ mem)
    (stencil : Fin H→Block cc→Cell (header*L)) (snap : PaddedSnapshot B oldRoom field)
    (fitted : (samePorts).stencil.Fits w start)
    (litFit : ∀j:Fin (cens).jobs,(flag j).Fits w start)
    (rootFit : ∀s t,((samePorts).bank s t).Fits w start)
    (present : ∀j:Fin (pool).card,Source (flag (j.cast (jCount degree).symm))
      (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) M₀ mem)
    (stamped : Source (samePorts).stencil stencil M₀ mem)
    (rootPages : ∀s t,Source ((samePorts).bank s t) (savedInput B oldRoom snap) M₀ mem)
    (arrivalFits : 2*(A).cap<2^b) :
    Source (samePorts).old (ownOld («b»:=b) B oldRoom) M₀ (after mem) ∧
      Source (samePorts).relay (ownArrivals («b»:=b) B incoming) M₀ (after mem) ∧
      Source (samePorts).stencil stencil M₀ (after mem) ∧
      (∀j:Fin (pool).card,Source (flag (j.cast (jCount degree).symm))
        (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) M₀ (after mem)) ∧
      ∀s t,Source ((samePorts).bank s t) (savedInput B oldRoom snap) M₀ (after mem):=by
  let eqn : (fund)=physical:=funded_setup (p:=p) B drift maxDegree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor blocks groups degree capacity
  let old:=Setup.oldAt eqn run.earlier
  let chips:=Setup.signAt eqn signal
  have axes : 2^(high+low)=S.groupCount age*2^k:=by
    rw [ageDim batch,pow_add,S.group_power ctl.base ctl.radix]
  have short : cc≤high+low:=by rw [B.commonDepth,ageDim batch];omega
  have donors : (physical).donors=2^k:=by change 2^(high+low-cc)=2^k;rw [ageDim batch,B.commonDepth];simp
  have pitch : 2^low=M₀*2^k:=pow_add _ _ _
  have packed : M₀*(physical).donors=2^low:=by rw [donors];exact pitch.symm
  let seen:=fun j:Fin (pool).card=>flag (j.cast (jCount degree).symm)
  have space : (physical).roof start<2^w:=(Setup.roof_at eqn start) ▸ safe.fund
  have port:=(funded_registers (funded_residual B) B.dimension run.ports)
  have oldFit (j : Block k): (old j).Fits w start:=safe.earlier _
  have chipFit (j : Fin (2*(A).cap)): (chips j).Fits w start:=tapSpace _
  have issued:=funded_channels («b»:=b) B oldRoom high low venue.lanes M₀ start old key chips (samePorts).stencil
    seen (samePorts).bank mem safe.saved oldFit space μ saved (ageDim batch) picked axes pitch short packed
    oldPos (Nat.two_pow_pos _) (Nat.two_pow_pos _) room oldPaid incoming chipFit taps stencil snap fitted
    (fun j=>litFit _) rootFit stamped present rootPages arrivalFits
  rw [Setup.read_at eqn start run.earlier key mem]
  have first : (samePorts).old=Expr.lookup ((physical).primary start) .row:=
    port.1.trans (congrArg (fun bank=>Expr.lookup bank .row) (Setup.primary_at eqn start))
  have second : (samePorts).relay=(physical).secondary start chips:=
    port.2.1.trans (Setup.secondary_at eqn start signal)
  rw [first,second]
  exact issued

/-- Whole original paid memory from the incoming stage-venue, the true selected
basis and the protected pre-funding signed, occupied, and root words. -/
theorem paid_from_previous
    (batch : e≤previous) (small : previous≤S.groupWidth k tail age)
    (rootRows : u.roots=roots batch small) (menu : u.atlas=atlas u.shape u.count)
    (grain : z=S.grainAt G.b p (age+1)) (degree : venue.degree=D) (capacity : venue.cap=(A).cap)
    (oldRoom : Fintype.card prior.V≤H) (mem : Memory w) (safe : run.Room) (ready : u.Ready)
    (blocks : venue.k=k) (groups : venue.groups=S.groupCount age) (oldPos : 0<venue.lanes)
    (peer : Fin H→Fin D→Option (Fin H)) (priorMem : Memory w) (priorStart : ℕ)
    (banks : IssuedBanks run.io H (S.groupCount age) venue.lanes)
    (held : stageVenue prior oldRoom run.io venue.lanes b priorStart peer priorMem)
    («protected» : ∀address,address<priorStart→mem address=priorMem address)
    (μ : DescentGL.Layout (high+low)) (picked : HEq μ B.frame.basis)
    (saved : mem (key).base=((DescentExterior.matrixCode μ).val:Word w))
    (incoming : Fin (2*(A).cap)→Fin H→Block cc→Fin L→Cell sig)
    (taps : ∀j:Fin (2*(A).cap),Source (signal (j.cast (congrArg (2*·) capacity.symm)))
      (fun v hi=>encode sig (physical).donors (fun l=>incoming j v hi
        (Fin.cast (by change 2^(high+low-cc)=L;rw [ageDim (batch.trans small)]) l))) M₀ mem)
    (stencil : Fin H→Block cc→Cell (header*L)) (snap : PaddedSnapshot B oldRoom field)
    (actorShape : (cens).jobs=(v₀).actor.shapes)
    (actorRows : (v₀).actor.hosts*(v₀).actor.chunksPerHost=H*chunks (2^cc) M₀)
    (actorRaster : ∀(j:Fin (pool).card) (pos:Row H (2^cc) M₀),
      mem ((FinalInputs.predecessor u).actor.base+j.val*(H*chunks (2^cc) M₀)+(row H (2^cc) M₀ pos).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) pos).val:Word w))
    (stamped : Source (samePorts).stencil stencil M₀ mem)
    (rootPages : ∀s t,Source ((samePorts).bank s t) (savedInput B oldRoom snap) M₀ mem)
    (fBits : ℕ)
    (order : W.graph.Edge↪ℕ) (names : DescentSharedCableNames.Stage.Host (Fin (S.groupCount age)) prior.V k↪ℕ)
    (panel : ∀v hi,stencil ((prior.vertex v).castLE oldRoom) hi=
      encode header L (Recorded.realPanel (reset:=B) rfl basis fBits header v hi))
    (signed : ∀j v hi lo,incoming j ((prior.vertex v).castLE oldRoom) hi lo=
      DescentSignedCableCodec.encode (Stage.signedPanel A order S prior.valid names
        (((block (oldIx hi lo)).1,v),(block (oldIx hi lo)).2) j))
    (up : small₀<2^fBits) (one : 1<2^fBits) (enough : L*mass<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows small₀ (2^(Z).n)≤2^header)
    (active : 0< mass) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*(A).degree))
    (countFits : mass<2^b) (arrivalFits : 2*(A).cap<2^b)

    (j : Fin (pool).card) (pos : Row H (2^cc) M₀) :
    (paidRAM mem) (((v₀).venue.original base).base+j.val*(H*chunks (2^cc) M₀)+(row H (2^cc) M₀ pos).val)=
      ((data (fun v hi=>payable (precision:=b) B recorded oldRoom (finProdFinEquiv (v,j)) hi) pos).val:Word w) :=by
  have positive : 0<(v₀).actor.shapes:=by
    rw [←actorShape,jCount degree]
    exact (by decide : 0<2).trans_le (two_le_roster_card (Z).graph rel dep)
  obtain ⟨tapSpace,stencilFits,litFit,bookFits⟩:=run.prior_funding_ports ready safe actorShape positive
  have found:=funded_registers (funded_residual B) B.dimension run.ports
  have fitted : (samePorts).stencil.Fits w start:=found.2.2.symm ▸ stencilFits
  have rootFit:=funded_bank_all (funded_residual B) B.dimension run.ports (fun op=>op.Fits w start) bookFits
  have present:=run.prior_funding_actors ready actorShape (jCount degree) actorRows
    (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom)) mem actorRaster
  have previous_:=original_pages prior oldRoom run.io peer banks held «protected»
  obtain ⟨old,relay,stored,lits,keys⟩:=paid_channels (p:=p) B drift maxDegree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor run blocks groups degree capacity oldRoom mem safe (batch.trans small)
    oldPos μ picked saved (fun x=>(previous_ x).2.1) (fun x=>(previous_ x).2.2)
    incoming tapSpace taps stencil snap fitted litFit rootFit present stamped rootPages arrivalFits
  exact paid_memory B recorded drift maxDegree payload e previous M nextM oldLanes primitiveLanes printedBits venue io
    floor run batch small rootRows menu grain degree capacity oldRoom mem safe stencil incoming snap fBits order names
    panel signed up one enough legal active quotaPos degreePos countFits arrivalFits stored old relay lits keys j pos

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
