import OAI.Hierarchy.DescentFundedJobCalendar
import OAI.Hierarchy.DescentNamedResetAtlas
import OAI.Hierarchy.DescentPhysicalResetDate

namespace OAI
/-! # The funded rows in the actual named reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentCompiler DescentSixParty DescentSixParty.ClosedReset.Window DescentDenseHostOrder
open Computability.VPVNP.BurstRAM PrivateRAM
open DescentFundedCensus DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
private theorem program_rows {left right : Shape} (eqn : left=right)
    (lhs : Fin left.jobs→Job left.bits) (rhs : Fin right.jobs→Job right.bits)
    (agree : ∀i j,i.val=j.val→HEq (lhs i) (rhs j)) (w base : ℕ) (m : Memory w) :
    program (s:=left) lhs w base=program (s:=right) rhs w base ∧ ticks (s:=left) lhs base=ticks (s:=right) rhs base ∧
    memory (s:=left) lhs base m=memory (s:=right) rhs base m :=by
  subst right
  have same:lhs=rhs:=funext fun i=>eq_of_heq (agree i i rfl)
  subst rhs
  exact ⟨rfl,rfl,rfl⟩

private theorem room_rows {left right : Shape} (eqn : left=right)
    (lhs : Fin left.jobs→Job left.bits) (rhs : Fin right.jobs→Job right.bits)
    (agree : ∀i j,i.val=j.val→HEq (lhs i) (rhs j)) (w base : ℕ) :
    DescentFundedCensus.Room (s:=left) lhs w base ↔ DescentFundedCensus.Room (s:=right) rhs w base :=by
  subst right
  have same:lhs=rhs:=funext fun i=>eq_of_heq (agree i i rfl)
  subst rhs
  rfl

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

theorem source_rows (degree : venue.degree=D) : (cens).jobs=(pool).card :=by
  change (roster ctl.board k (GroupStage.depthBound venue.degree n f g)).card=(pool).card
  rw [degree]
  exact (funded_row_count B).symm

/-- The predecessor normalization and signed-arrival count use exactly the
selected stage's old host/group/block dimensions and output packing. -/
theorem funded_setup (blocks : venue.k=k) (groups : venue.groups=S.groupCount age)
    (degree : venue.degree=D) (capacity : venue.cap=(A).cap) :
    (fund)=(⟨venue.hosts,S.groupCount age,2^k,venue.lanes,2^e,venue.paidBits,
      S.groupWidth k tail age-e,e+k,B.terminals.commonDepth,(A).degree,(A).cap,2^e⟩:Setup) :=by
  change (⟨venue.hosts,venue.groups,2^venue.k,venue.lanes,2^e,venue.paidBits,
    S.groupWidth k tail age-e,e+k,S.groupWidth k tail age,venue.degree,venue.cap,2^e⟩:Setup)=_
  rw [groups,blocks,B.commonDepth,degree,capacity,prior.branch]

include recorded

/-- Every physical lookup in FinalInputs.jobs, on the same actor and root
bank addresses, is the lookup for the genuine charged row of this branch.
The numerical index on both sides is the physical ordinal j. -/
theorem funded_facts (batch : e≤previous) (small : previous≤S.groupWidth k tail age)
    (rootRows : u.roots=roots batch small) (menu : u.atlas=atlas u.shape u.count)
    (grain : z=S.grainAt G.b p (age+1)) (degree : venue.degree=D) (capacity : venue.cap=(A).cap) :
    ∀j:Fin (cens).jobs,∃x:Fin (pool).card,x.val=j.val ∧
      run.jobs j=compile (Ht:=dep) (Z).graph C (Z).width ((Z).unit/p) (cens).bits (A).cap f (A).degree (A).cap
        u.roots.field (phase).S.t samePorts (flag j) (shapes B x) :=by
  intro j
  let x:=j.cast (source_rows (p:=p) B drift maxDegree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor degree)
  refine ⟨x,rfl,?_⟩
  have menuDegree : u.atlas.boardDegree=h:=by rw [menu];rfl
  have board : HEq u.atlas.board ctl.board:=by rw [menu];rfl
  have rootHeight : u.roots.Ht=dep:=by rw [rootRows];change GroupStage.depthBound venue.degree n f g=dep;rw [degree]
  have numericC : u.atlas.C=C:=by rw [menu];rfl
  have numericPacket : u.atlas.packet=ctl.bitsR:=by rw [menu];rfl
  have numericUnits : u.atlas.groupDigits=ResetInput.calendarLanes S G.b (age+1):=by rw [menu];rfl
  have capId : (fund).capacity=(A).cap:=capacity
  have dg : (fund).degree=D:=degree
  have gain : (a).depthCut=f:=rfl
  unfold jobs
  rw [numericC,numericPacket,numericUnits,B.width,funded_units B recorded grain,capId,gain,dg,prior.branch]
  symm
  exact public_row_eq (Z).graph u.atlas.board B.dimension menuDegree.symm (B.graph.trans board.symm)
    (funded_residual B) rootHeight.symm samePorts run.ports (fundedPorts_eq ..) C ctl.bitsR
    (ResetInput.calendarLanes S G.b (age+1)) (cens).bits (A).cap f D u.roots.field (phase).S.t
    (flag j) x (j.cast run.roleCount) rfl

local notation "actualShape" => (⟨(pool).card,venue.hosts,2^B.terminals.commonDepth,2^e,(cens).bits,(cens).broadcast⟩:Shape)
local notation "nRows" eg:arg => source_rows (p:=p) B drift maxDegree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor eg

private theorem matching_rows (batch : e≤previous) (small : previous≤S.groupWidth k tail age)
    (rootRows : u.roots=roots batch small) (menu : u.atlas=atlas u.shape u.count)
    (grain : z=S.grainAt G.b p (age+1)) (degree : venue.degree=D) (capacity : venue.cap=(A).cap) :
    let actual:=fun j : Fin (pool).card=>compile (Ht:=dep) (Z).graph C (Z).width ((Z).unit/p) (cens).bits (A).cap f (A).degree
      (A).cap u.roots.field (phase).S.t samePorts (flag (j.cast (nRows degree).symm)) (shapes B j)
    (cens)=actualShape ∧ ∀i j,i.val=j.val→HEq (run.jobs i) (actual j) :=by
  intro actual
  have count:=nRows degree
  have shape : (cens)=actualShape:=by
    change (⟨(roster ctl.board k (GroupStage.depthBound venue.degree n f g)).card,venue.hosts,2^(S.groupWidth k tail age),2^e,
      (cens).bits,(cens).broadcast⟩:Shape)=_
    rw [←B.commonDepth]
    exact congrArg (fun v=>(⟨v,venue.hosts,2^B.terminals.commonDepth,2^e,(cens).bits,(cens).broadcast⟩:Shape)) count
  refine ⟨shape,?_⟩
  intro i j same
  obtain ⟨j',eqr,read⟩:=funded_facts B recorded drift maxDegree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor run batch small rootRows menu grain degree capacity i
  have atJ:j'=j:=Fin.ext (eqr.trans same)
  subst j'
  have origin:j.cast count.symm=i:=Fin.ext same.symm
  dsimp only [actual]
  rw [origin]
  exact heq_of_eq read

/-- The whole-table identity uses the real dated dictionary and gate expressions.
Consequently its printed finite program, its clock, and its returned memory are
identical on every input state. -/
theorem funded_array (batch : e≤previous) (small : previous≤S.groupWidth k tail age)
    (rootRows : u.roots=roots batch small) (menu : u.atlas=atlas u.shape u.count)
    (grain : z=S.grainAt G.b p (age+1)) (degree : venue.degree=D) (capacity : venue.cap=(A).cap)
    (base : ℕ) (m : Memory w) :
    let actual:=fun j : Fin (pool).card=>compile (Ht:=dep) (Z).graph C (Z).width ((Z).unit/p) (cens).bits (A).cap f (A).degree
      (A).cap u.roots.field (phase).S.t samePorts (flag (j.cast (nRows degree).symm)) (shapes B j)
    program (s:=cens) run.jobs w base = program (s:=actualShape) actual w base ∧
    ticks (s:=cens) run.jobs base = ticks (s:=actualShape) actual base ∧
    memory (s:=cens) run.jobs base m = memory (s:=actualShape) actual base m :=by
  intro actual
  have h:=matching_rows B recorded drift maxDegree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor run batch small rootRows menu grain degree capacity
  exact program_rows h.1 run.jobs actual h.2 w base m

theorem funded_room_array (batch : e≤previous) (small : previous≤S.groupWidth k tail age)
    (rootRows : u.roots=roots batch small) (menu : u.atlas=atlas u.shape u.count)
    (grain : z=S.grainAt G.b p (age+1)) (degree : venue.degree=D) (capacity : venue.cap=(A).cap)
    (base : ℕ) :
    let actual:=fun j : Fin (pool).card=>compile (Ht:=dep) (Z).graph C (Z).width ((Z).unit/p) (cens).bits (A).cap f (A).degree
      (A).cap u.roots.field (phase).S.t samePorts (flag (j.cast (nRows degree).symm)) (shapes B j)
    DescentFundedCensus.Room (s:=cens) run.jobs w base ↔ DescentFundedCensus.Room (s:=actualShape) actual w base :=by
  intro actual
  have h:=matching_rows B recorded drift maxDegree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor run batch small rootRows menu grain degree capacity
  exact room_rows h.1 run.jobs actual h.2 w base

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
