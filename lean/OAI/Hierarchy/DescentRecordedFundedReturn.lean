import OAI.Hierarchy.DescentNamedPaidStencilReturn

namespace OAI
/-! # The six original funded channels recovered from one actual named reset date -/
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

local notation "stc" => (a).throughStencil u.shape foot u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "tc" => (a).throughStencilTicks u.shape foot u.count u.hub u.g u.Y u.sourceRows u.oldDegree w
local notation "rc" => (a).rootPhase u.shape foot u.count u.hub u.g u.Y u.roots w
open DescentPlainTerminal.Suffix DescentFallbackPeriod DescentFallbackPeriod.Projected
open ThreeFlat.RAM PhysicalProcedure

local notation "rawHost" pad:arg => prior.vertex.trans (Fin.castLEEmb pad)

/-- The fallback words have already been recorded in the prepared root book.
All numbering, signing and operand writes preserve these exact original pages. -/
theorem reached_paid_root_words (ready : u.Ready) (oldRoom : Fintype.card prior.V≤H)
    (before measured result : Memory w) (scanned : (stc).Exec before measured tc)
    (completed : u.throughOperandDate.Runs before result) (snap : PaddedSnapshot B oldRoom field)
    (rootPages : ∀s t,Source ((samePorts).bank s t) (savedInput B oldRoom snap) M₀ ((rc).preparedImage u.book u.bookFits measured)) :
    ∀s t,Source ((samePorts).bank s t) (savedInput B oldRoom snap) M₀ result:=by
  have reached:=u.prefix_unchanged ready (afterRoots:=(rc).preparedImage u.book u.bookFits measured)
    (by intro p q t controller;exact Procedure.Exec.then scanned ((rc).prepared_any u.book u.bookFits measured).1 controller) completed
  have entered:=funded_bank_all (funded_residual B) B.dimension run.ports (fun e=>e.Fits w ((rc).preparedEnd u.book))
    (fun s t=>(rc).gathered_fits u.book u.bookFits (s,.inr t))
  intro s t pos
  exact (eval_below _ _ _ _ (entered s t) reached).trans (rootPages s t pos)

/-- The old stage-venue, the attained GL and root print, and the original
occupied-site raster determine every funded word at the actual named
address on the one fully executed reset. -/
theorem reached_funded_words
    (batch : e≤previous) (small : previous≤c₀) (listed : u.roots=roots batch small)
    (menu : u.atlas=atlas u.shape u.count) (grain : z=S.grainAt G.b p (age+1))
    (degree : venue.degree=D) (capacity : venue.cap=(A).cap) (hosts : S.hostSize age=H)
    (blocks : venue.k=k) (groups : venue.groups=S.groupCount age) (wirePitch : venue.lanes=2^previous)
    (oldRoom : Fintype.card prior.V≤H) (ready : u.Ready) (safe : run.Room)
    (same : run.io=io) (peer : Fin H→Fin D→Option (Fin H)) (priorStart : ℕ) (floorLE : priorStart≤foot)
    (before measured result : Memory w) (held : stageVenue prior oldRoom io venue.lanes b priorStart peer before)
    (issued : IssuedBanks io H (S.groupCount age) venue.lanes)
    (wireRoom : ∀(x : Block k)(j : Fin (2*(A).cap)),(io.wire x.val j.val).Fits w priorStart ∧
      H*chunks (S.groupCount age) venue.lanes≤(io.wire x.val j.val).size)
    (scanned : (stc).Exec before measured tc) (completed : u.throughOperandDate.Runs before result)
    (μ : DescentGL.Layout (high+low)) (chosen : HEq μ basis)
    (saved : measured (phase).saved=((DescentExterior.matrixCode μ).val:Word w))
    (actorShape : (cens).jobs=(v₀).actor.shapes)
    (actorRows : (v₀).actor.hosts*(v₀).actor.chunksPerHost=H*chunks (2^cc) M₀)
    (actorRaster : ∀(j:Fin (pool).card) (pos:Row H (2^cc) M₀),
      result ((FinalInputs.predecessor u).actor.base+j.val*(H*chunks (2^cc) M₀)+(row H (2^cc) M₀ pos).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) pos).val:Word w))
    (snap : PaddedSnapshot B oldRoom field)
    (rootPages : ∀s t,Source ((samePorts).bank s t) (savedInput B oldRoom snap) M₀ ((rc).preparedImage u.book u.bookFits measured))
    (fBits : ℕ) (printed : PackedFlow.Padded.Published (h:=high) (l:=low) M₀ header (phase).output (rawHost oldRoom)
      (Recorded.realPanel (reset:=B) (ageDim (batch.trans small)) μ fBits header) measured)
    (up : small₀<2^fBits) (one : 1<2^fBits) (enough : L*mass<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows small₀ (2^(Z).n)≤2^header)
    (active : 0< mass) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*(A).degree))
    (countFits : mass<2^b) (arrivalFits : 2*(A).cap<2^b)
    (j : Fin (pool).card) (pos : Row H (2^cc) M₀) :
    (paidRAM result) (((v₀).venue.original base).base+j.val*(H*chunks (2^cc) M₀)+(row H (2^cc) M₀ pos).val)=
      ((data (fun v hi=>payable (precision:=b) B recorded oldRoom (finProdFinEquiv (v,j)) hi) pos).val:Word w):=by
  have exist:0<(v₀).actor.shapes:=by
    rw [←actorShape,jCount degree]
    exact (by decide : 0<2).trans_le (two_le_roster_card (Z).graph rel dep)
  have signed:=reached_paid_signs (p:=p) B drift maxDegree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor run batch small listed degree capacity hosts wirePitch oldRoom ready peer priorStart before measured
    result held wireRoom floorLE scanned completed μ chosen saved
  obtain ⟨head,read,truth⟩:=reached_paid_stencil (p:=p) B drift maxDegree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor run ready safe oldRoom actorShape exist actorRows hosts before measured result
    scanned completed (ageDim (batch.trans small)) μ chosen printed
  have keys:=reached_paid_root_words (p:=p) B drift maxDegree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor run ready oldRoom before measured result scanned completed snap rootPages
  obtain ⟨out,exe,_,kept⟩:=u.run_to_operands ready before
  have eqn:=exec_unique _ before result out completed exe
  have still:∀address,address<priorStart→ result address=before address:=fun address x=>(congrFun eqn address).trans (kept address (.inl (x.trans_le floorLE)))
  have stock:stageVenue prior oldRoom run.io venue.lanes b priorStart peer before:=by rw [same];exact held
  have banks:IssuedBanks run.io H (S.groupCount age) venue.lanes:=by rw [same];exact issued
  exact paid_from_previous B recorded drift maxDegree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor run batch small listed menu grain degree capacity oldRoom result safe ready blocks groups
    (by rw [wirePitch];exact Nat.two_pow_pos _) peer before priorStart banks stock still μ chosen signed.2
    (fundingSign B oldRoom) signed.1 head snap actorShape actorRows actorRaster read keys fBits _ _
    truth (funding_sign_at B oldRoom) up one enough legal active quotaPos degreePos countFits arrivalFits j pos

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
