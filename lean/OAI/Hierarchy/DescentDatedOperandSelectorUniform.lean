import OAI.Hierarchy.DescentDatedOperandHeadUniform
import OAI.Hierarchy.DescentDatedOperandNativePreparation

namespace OAI
/-! # The complete original operand program and its output ports from the public date layout -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentRawCablePanel DescentHaloWalkRAM
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentOrdinaryAtomFieldRAM
open DescentOperandStateBanks ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

namespace ArgumentPlan
variable (p : ArgumentPlan) (c : StaticCore)
local notation "H₀" => p.headCode c
local notation "e₀" => c.prefixProgram.material.extent
local notation "fmt₀" => c.prefixProgram.material.depot
local notation "P₀" => breadth (fmt₀).degree
local notation "l₀" => p.resolver

/-- The three finite index identifications have no data-dependent content. -/
structure SelectorShape : Prop where
  blocks : (l₀).blocks=p.vector.radix
  args : (l₀).operands=p.vector.operands
  material : (l₀).blocks=(e₀).blocks

def selectorWidths : Fin 4 → ℕ := ![(e₀).fieldBits,(l₀).size+2,p.born.bits,Packed.bits P₀]
def selectorBits :=max (max (e₀).fieldBits ((l₀).size+2)) (max p.born.bits (Packed.bits P₀))
def selectorGeometry : Geometry :=
  ⟨(l₀).hosts,(l₀).groups,(l₀).lanes,(l₀).jobs,P₀,(fmt₀).blocks,(fmt₀).degree,(fmt₀).cap,
    p.selectorBits c,(l₀).size+2⟩
def selectorNarrowStart := (H₀).wideHeads.endAddress (p.headBound c)
def selectorCastStart := (H₀).narrowHeads.endAddress (p.selectorNarrowStart c)
def selectorStart :=DescentDatedOperandCasts.stop (p.selectorBits c) (l₀).lanes (p.selectorCastStart c)

def wideSocket (key : (H₀).WideHead) : Expr :=
  .lookup ((H₀).wideHeads.bank (p.headBound c) ((H₀).wideHeadNumber key)) .row
def narrowSocket (key : (H₀).NarrowHead) : Expr :=
  .lookup ((H₀).narrowHeads.bank (p.selectorNarrowStart c) ((H₀).narrowHeadNumber key)) .row

def selectorSources (s : p.SelectorShape c) : Sources (p.selectorGeometry c) :=
  let block:=fun j=>((l₀).index.symm j).1.cast s.material
  let up:=DescentDatedOperandCasts.expr (p.selectorWidths c) (p.selectorBits c) (l₀).lanes (p.selectorCastStart c)
  let origin:=fun j f=>
    let (x,n,_):=(l₀).index.symm j
    DescentOrdinaryOriginPorts.expr p.originChart (p.selectorBits c) p.routedStart p.portFloor (x.cast s.blocks) n f
  let prior:=fun j (f : Fin 4)=>
    let (x,n,arg):=(l₀).index.symm j
    let bank:=DescentDatedPriorOperand.previousBank (l₀) (p.vector.out p.vectorStart) x (page (f.castLE (by decide : 4≤7)) arg)
    ScalarOperand.headerExpr (p.oldStart c) ((l₀).size+2) (l₀).nodes (l₀).lanes bank n
  let mouth:=fun j f=>
    let (x,n,arg):=(l₀).index.symm j
    let bank:=p.mouthChart.returned p.portEnd (arg.cast (s.args.trans p.newArgs.symm)) f (x.cast s.blocks)
    ScalarOperand.headerExpr (p.mouthStart c) p.born.bits (l₀).nodes (l₀).lanes bank n
  ⟨origin,fun j f=>up 1 (prior j f),fun j f=>up 2 (mouth j f),
   fun j f i=>up 0 (p.wideSocket c (.inl (block j,f,i))),
   fun i=>up 3 (p.narrowSocket c (.inl i)),
   fun j f i=>up 0 (p.wideSocket c (.inr (.inl (block j,f,i)))),
   fun j f i=>up 0 (p.wideSocket c (.inr (.inr (block j,f,i)))),
   fun i=>up 3 (p.narrowSocket c (.inr i))⟩

def selectorPort (s : p.SelectorShape c) (j : Fin (l₀).jobs) (f : Fin 8) : Expr :=
  SortedInput.output (p.selectorGeometry c) (p.selectorSources c s) (p.selectorStart c) j f

def ticketPreparation (s : p.SelectorShape c) (chart : c.prefixProgram.Chart) (w : ℕ)
    (pg : Fin (7*p.vector.operands)) : NativePhase w :=
  let cast:=DescentDatedOperandCasts.phase (p.selectorWidths c) (p.selectorBits c) (l₀).lanes (p.selectorCastStart c) w
  let resolve:=SortedInput.program (p.selectorGeometry c) (p.selectorSources c s) (p.selectorStart c) (e₀).oldHosts
    c.prefixProgram.material.setup.hostPitch (H₀).rankBanks.endpoints (p.clip.ports p.signedEnd).roster w
  (p.originAndMouth (p.selectorBits c) w pg).seq (((((p.early c w).seq ((H₀).native chart w)).seq cast).seq resolve))

theorem selector_port_congr {q : ArgumentPlan} {t : StaticCore} (plans : p=q) (cores : c=t)
    (s : p.SelectorShape c) (s' : q.SelectorShape t) (j : Fin p.resolver.jobs) (k : Fin q.resolver.jobs)
    (index : j.val=k.val) (f : Fin 8) : p.selectorPort c s j f=q.selectorPort t s' k f :=by
  subst q
  subst t
  cases Fin.ext index
  rfl

theorem preparation_congr {q : ArgumentPlan} {t : StaticCore} (plans : p=q) (cores : c=t)
    (s : p.SelectorShape c) (s' : q.SelectorShape t) (chart : c.prefixProgram.Chart) (chart' : t.prefixProgram.Chart)
    (w : ℕ) (i : Fin (7*p.vector.operands)) (j : Fin (7*q.vector.operands)) (index : i.val=j.val) :
    p.ticketPreparation c s chart w i=q.ticketPreparation t s' chart' w j :=by
  subst q
  subst t
  cases Fin.ext index
  rfl
end ArgumentPlan

section
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor : ℕ) (A : v.ArgumentEntry)
  (m : A.Match v floor) (s : v.VectorShape) (blocks : v.resolver.blocks=v.material.blocks)
local notation "p₀" => v.bareArguments floor A m
local notation "c₀" => v.staticCore floor

include s blocks in
theorem selectorShape : (p₀).SelectorShape (c₀) :=⟨s.blocks,s.operands,blocks⟩

theorem ticket_expression_plan (cs : v.SignedChart) (j : Fin v.resolver.jobs) (f : Fin 8) :
    (p₀).selectorPort (c₀) (v.selectorShape floor A m s blocks) j f=
      v.nativeTicketExpr floor cs A m s blocks j f :=rfl

attribute [local irreducible] SortedInput.program DescentDatedOperandCasts.phase

theorem ticket_preparation_plan (cs : v.SignedChart) (w : ℕ) (pg : Fin (7*v.vector.operands)) :
    (p₀).ticketPreparation (c₀) (v.selectorShape floor A m s blocks) (v.publicSignedChart floor cs) w pg=
      v.nativeTicketPreparation floor w cs A m s blocks pg :=by
  unfold ArgumentPlan.ticketPreparation nativeTicketPreparation originalSourcePhase
  apply congrArg₂ NativePhase.seq
  · exact v.origin_mouth_plan floor (v.operandShortBits) w A m pg
  · apply congrArg₂ NativePhase.seq
    · apply congrArg₂ NativePhase.seq
      · exact congrArg₂ NativePhase.seq (v.early_plan floor w A m) (v.actual_head_native floor w cs)
      · rfl
    · rfl
end

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
