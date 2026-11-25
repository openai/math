import OAI.Hierarchy.DescentFundedPhase
import OAI.Hierarchy.DescentFundedCalendar

namespace OAI
/-! # The physical funded lookup in public calendar order -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentFundedCensus DescentDenseHostOrder DescentDatedAddressBook
open DescentPhysicalOrder DescentPaidResidentCount
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

theorem funded_rows_eq {n n' d k k' Ht : ℕ} (A : NonlinearExpanders.Graph n d) (B : NonlinearExpanders.Graph n' d)
    (dim : n=n') (same : HEq A B) (window : k=k') (jobs : (DescentDenseHostOrder.roster A k Ht).card=(DescentDenseHostOrder.roster B k' Ht).card)
    (src : DescentFundedCensus.Ports k n) (dst : DescentFundedCensus.Ports k' n') (ports : HEq src dst)
    (C packet units bits cap f degree field stencil : ℕ) (flag : Expr) (j : Fin (DescentDenseHostOrder.roster A k Ht).card) :
    compile (Ht:=Ht) A C packet units bits cap f degree cap field stencil src flag (ActorSetup.shapeAt A k Ht j)=
    compile (Ht:=Ht) B C packet units bits cap f degree cap field stencil dst flag (ActorSetup.shapeAt B k' Ht (j.cast jobs)) :=by
  subst n'
  subst k'
  obtain rfl:=eq_of_heq same
  obtain rfl:=eq_of_heq ports
  rfl

/-- Transport only the finite domain of the exceptional bank. The numerical
expressions and held source coordinates are the ones already published. -/
def fundedPorts {r n k m : ℕ} (depth : r=k) (size : n=m) (dst : DescentFundedCensus.Ports k m) : DescentFundedCensus.Ports r n :=by
  subst k
  subst m
  exact dst

theorem fundedPorts_eq {r n k m : ℕ} (depth : r=k) (size : n=m) (dst : DescentFundedCensus.Ports k m) :
    HEq (fundedPorts depth size dst) dst :=by
  subst k
  subst m
  rfl

/-- Two zero-based row numbers transported through the original ordered
roster and dimension equalities select the same genuine lookup. -/
theorem public_row_eq {n n' d d' k k' Ht Ht' : ℕ} (board : NonlinearExpanders.Graph n d)
    (menu : NonlinearExpanders.Graph n' d') (size : n=n') (degree : d=d') (shape : HEq board menu)
    (width : k=k') (height : Ht=Ht') (src : DescentFundedCensus.Ports k n) (dst : DescentFundedCensus.Ports k' n') (ports : HEq src dst)
    (C packet units bits cap f D field stencil : ℕ) (flag : Expr) (x : Fin (DescentDenseHostOrder.roster board k Ht).card)
    (y : Fin (DescentDenseHostOrder.roster menu k' Ht').card) (index : x.val=y.val) :
    compile (Ht:=Ht) board C packet units bits cap f D cap field stencil src flag (ActorSetup.shapeAt board k Ht x)=
    compile (Ht:=Ht') menu C packet units bits cap f D cap field stencil dst flag (ActorSetup.shapeAt menu k' Ht' y) :=by
  subst d'
  subst n'
  subst k'
  subst Ht'
  obtain rfl:=eq_of_heq shape
  obtain rfl:=eq_of_heq ports
  obtain rfl:=Fin.ext index
  rfl

variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {cap:Reached W G q ε S k i z D wire hist} (B:ClosedReset cap ctl)
local notation "A" => cap.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "r" => ((Z).k-(T).commonDepth)
local notation "dep" => GroupStage.depthBound D n f g
local notation "pool" => DescentDenseHostOrder.roster (Z).graph r dep
local notation "printed" => DescentDenseHostOrder.roster ctl.board k dep

theorem funded_residual : r=k :=by rw [B.keyWidth,B.commonDepth];omega

theorem funded_row_count : (pool).card=(printed).card := by
  rw [funded_residual B]
  exact rosterCard_board (Z).graph ctl.board B.dimension B.graph _ _

theorem funded_units {p:ℕ} (r₀:B.Recorded p) (grain:z=S.grainAt G.b p (i+1)) :
    (Z).unit/p=ResetInput.calendarLanes S G.b (i+1) :=by
  rw [ResetInput.calendar_fit Z S G.b p (i+1) (B.unit.trans (congrArg (·*G.b) grain))]
  exact Nat.mul_div_cancel _ r₀.positive

/-- The bank and stencil selectors are unchanged under the public residue/dimension
casts. Each original job is the same program and same lookup as the published
calendar row, including zero traffic, permanent rotor sites, and fallback leaves. -/
theorem funded_job_calendar {p:ℕ} (r₀:B.Recorded p) (grain:z=S.grainAt G.b p (i+1))
    (b field stencil : ℕ) (src : DescentFundedCensus.Ports r (Z).n) (dst : DescentFundedCensus.Ports k n) (ports : HEq src dst)
    (flag : Expr) (j : Fin (pool).card) :
    compile (Ht:=dep) (Z).graph C (Z).width ((Z).unit/p) b (A).cap f (A).degree (A).cap field stencil src flag (shapes B j)=
    compile (Ht:=dep) ctl.board C ctl.bitsR (ResetInput.calendarLanes S G.b (i+1)) b (A).cap f D (A).cap field stencil
      dst flag (ActorSetup.shapeAt ctl.board k dep (j.cast (funded_row_count B))) :=by
  rw [B.width,funded_units B r₀ grain,cap.branch]
  exact funded_rows_eq (Z).graph ctl.board B.dimension B.graph (funded_residual B) (funded_row_count B)
    src dst ports C ctl.bitsR (ResetInput.calendarLanes S G.b (i+1)) b (A).cap f D field stencil flag j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
