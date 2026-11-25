import OAI.Hierarchy.DescentDatedSortedOperandProgram
import OAI.Hierarchy.DescentDatedSortedOperandAdapter
import OAI.Hierarchy.DescentDatedReadPipelineFee
import OAI.Hierarchy.DescentDatedSortedOperandRates
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Cost of the broadcast and native lookup translating an ordinary W ordinal -/
namespace Hierarchy.DescentDatedOperandReadPipeline.SortedInput
open DescentDatedSourcePathDirectory DescentSIMDLookup DescentSharedLeafLookup
open DescentDatedOperandSelectionRun DescentSixParty.Chronology DescentCompiler.TerminalScale
open DescentStaticWordColumn DescentArgumentWidthArithmetic ProtocolRAM
noncomputable section
variable (g : Geometry)
local notation "P" => g.paths
local notation "M" => g.lanes
local notation "H" => g.hosts
local notation "G" => g.groups

theorem port_work (base oldHosts : ℕ) (visited sorted : Bank) (s : Fin P) :
    (Broadcast.port g base oldHosts visited sorted s).work≤portWork P :=by
  let B:=Broadcast.layout g base visited
  let actor:=Expr.lookup B.start .row
  have sub (x : Expr) : (x.atRow actor).work≤x.work*8:=by
    induction x <;> simp only [actor,Expr.atRow,Expr.work,Nat.add_mul,Nat.one_mul] at * <;> omega
  have limit:=sub (Sorted.expr visited sorted oldHosts s)
  have high : (Sorted.expr visited sorted oldHosts s).work≤(P+1)*(30+8*P):=
    Sorted.expr_work visited sorted s
  change 7+(7+1+1+((Sorted.expr visited sorted oldHosts s).atRow actor).work+1)+1+5≤_
  dsimp [portWork]
  omega

/-- The new header port is one fixed packed-bank read irrespective of prior path count. -/
theorem sources_work (s : Sources g) (base limit : ℕ) (inputs : Sources.Work g s limit)
    (seven : 7≤limit) : Sources.Work g (sources g s base) limit :=by
  refine ⟨?_,inputs.prior,inputs.mouth,inputs.old,inputs.path,inputs.anchor,inputs.raw,inputs.rank⟩
  intro j f
  by_cases path : f=1
  · simpa only [sources,ite_eq_left path,word,lookup,Expr.work] using seven
  · simpa only [sources,ite_eq_right path] using inputs.origin j f

theorem selection_charge (s : Sources g) (hostBase oldHosts base w h ratio short U : ℕ) (visited sorted : Bank)
    (inputs : Sources.Work g s 32) (bound : ∀i,g.coefficientInputs 32 short i≤U)
    (fit : purchase g*M≤ h/2) (bus : w≤ratio*h) (fill : h≤M*short) :
    let ports:=Broadcast.port g hostBase oldHosts visited sorted
    (phase g s ports base w).wordInvoice≤
      U^22*ratio*(h+H*h+H*G*short)+U^22*ratio*(2^(h/2)*h) :=by
  intro ports
  let args:=headInputs g s
  have keys (j i) : (args j i).work≤32:=by fin_cases i <;> exact inputs.origin j _
  have bill:=stage_word_bill (layout g 1 P) (key g) (fun _=>0)
    (fun p=>args (finProdFinEquiv.symm p).1) (fun _=>ports)
    base w h ratio short 32 (portWork P) bus fill (family_room g (by decide : 2≤17) fit)
    (selector_room g 4 fit) (fun p i=>keys _ i) (fun _ t=>port_work g hostBase oldHosts visited sorted t)
  let r:=readFactor 1 2 P 32 (portWork P)
  let cells:=h+H*h+H*G*short
  change (phase g s ports base w).wordInvoice≤r*ratio*(g.jobs*1+1)*cells+r*ratio*(g.jobs*1+1)*2^(h/2)*h at bill
  have many : r*(g.jobs*1+1)≤U^22:=factor g short U bound
  calc
    _ ≤ r*ratio*(g.jobs*1+1)*cells+r*ratio*(g.jobs*1+1)*2^(h/2)*h:=bill
    _ = (r*(g.jobs*1+1))*ratio*cells+(r*(g.jobs*1+1))*ratio*(2^(h/2)*h):=by ring
    _ ≤ _:=by change _≤U^22*ratio*cells+_;gcongr

theorem broadcast_charge (base oldHosts pitch w h ratio short U : ℕ)
    (width : 0<g.digitBits) (lanes : 0<M) (bound : ∀i,g.coefficientInputs 32 short i≤U)
    (fit : purchase g*M≤h/2) (bus : w≤ratio*h) (fill : h≤M*short) :
    (Broadcast.phase g base oldHosts pitch w).wordInvoice≤
      U^22*ratio*(h+H*h+H*G*short)+U^22*ratio*(2^(h/2)*h) :=by
  let I:=Broadcast.image g base oldHosts pitch w
  let rows:=H*chunks G M
  let a:=g.digitBits
  have paid : 18*a*M≤h/2:=(Nat.mul_le_mul_right M (Nat.le_max_left _ _)).trans fit
  have footprint:=broadcast_size rows a M h width lanes paid
  have size : I.length≤2*(2*rows+1)+2^(h/2):=by
    change (base+2*2^(Nat.clog 2 rows)+2^(Nat.clog 2 ((M+1)*2^a)))-base≤_
    rw [Nat.add_assoc, Nat.add_sub_cancel_left]
    exact footprint
  have text:=I.hardware.2
  have raw : 4+10*I.length+7*names I.program≤8192*((0+1)*(1+rows)+(0+1)*2^(h/2)):=by
    rw [text]
    omega
  have bill:=DescentDatedSeedStartup.page_scan_words H G M short h w ratio 0 8192 _ fill bus raw
  change (Broadcast.phase g base oldHosts pitch w).wordInvoice≤_ at bill
  have big : 8192≤U:=bound 0
  have rate : 8192≤U^22:=raise (by omega) (one big) (by decide)
  simp only [Nat.zero_add,Nat.mul_one] at bill
  exact bill.trans (by rw [←Nat.mul_assoc (U^22*ratio) (2^(h/2)) h];gcongr)

/-- The original five lookups follow the paid translation and use its one-register result. -/
theorem program_charge (s : Sources g) (base oldHosts pitch w h ratio short U : ℕ) (visited sorted : Bank)
    (inputs : Sources.Work g s 32) (width : 0<g.digitBits) (lanes : 0<M)
    (bound : ∀i,g.coefficientInputs 32 short i≤U) (fit : purchase g*M≤h/2) (bus : w≤ratio*h)
    (fill : h≤M*short) :
    let each:=U^22*ratio*(h+H*h+H*G*short)+U^22*ratio*(2^(h/2)*h)
    (program g s base oldHosts pitch visited sorted w).wordInvoice≤7*each+finalCharge h ratio ∧
      ∀j f,(output g s base j f).work≤745 :=by
  intro each
  let start:=Broadcast.finish g base
  have fst:=broadcast_charge g base oldHosts pitch w h ratio short U width lanes bound fit bus fill
  have snd:=selection_charge g s base oldHosts start w h ratio short U visited sorted inputs bound fit bus fill
  have ready:=sources_work g s start 32 inputs (by decide)
  have core:=phase_charge g (sources g s start) (readBase g base) w h ratio short 32 fit bus fill ready (by decide)
  have rates:=(selector_rates g 32 short U bound).2.2.1
  have paid (q : Fin 5) : scanCharge g q h ratio short 32≤each:=by
    unfold scanCharge
    dsimp only [each]
    rw [←Nat.mul_assoc (U^22*ratio) (2^(h/2)) h]
    gcongr <;> exact rates q
  constructor
  · unfold program
    simp only [NativePhase.wordInvoice_seq]
    change _≤each at fst snd
    change (DescentDatedOperandReadPipeline.phase g (sources g s start) (readBase g base) w).wordInvoice≤_ at core
    have a:=paid 0;have b:=paid 1;have c:=paid 2;have d:=paid 3;have e:=paid 4
    dsimp only [start] at snd core
    omega
  · exact expression_charge g (sources g s start) (readBase g base) 32 ready (by decide)

end
end Hierarchy.DescentDatedOperandReadPipeline.SortedInput

end OAI
