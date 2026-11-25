import OAI.Hierarchy.DescentContactPreROMCatalog
import OAI.Hierarchy.DescentContactPreROMViews
import OAI.Hierarchy.DescentContactPreROMValues

namespace OAI
/-! # From the authentic old rotor window and endpoint words to all final short contact markers -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentFallbackPeriod.Projected DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable (A : Layout) {ports w : ℕ} (board : NonlinearExpanders.Graph A.n ports)
variable (boardReads : Fin A.oldFields→Expr) (prior : Bool→Fin A.half→Fin 5→Expr)
local notation "lifted" => DescentContactProbePitch.lift (S:=A.shapes)

structure Space (w : ℕ) : Prop where
  extent : A.endAddress<2^w
  marker : A.batch*max (A.fieldBits*8) A.outputBits≤w/2
  oldRow : ∀i,(boardReads i).Fits w A.first
  priorRow : ∀s j k,(prior s j k).Fits w A.first

def «fields» : Fin A.jobs→Fin 8→Expr :=
  A.rowFields (fun s j k=>A.priorView (prior s j k)) (fun s j f=>A.rawView (A.view s j f)) A.shapeView

variable (space : A.Space boardReads prior w)
include space in
theorem fields_fit (j : Fin A.jobs) (i : Fin 8) : (A.fields prior j i).Fits w A.markerBase := by
  let sq:=finProdFinEquiv.symm j
  let sd:=finProdFinEquiv.symm sq.2
  have room : A.markerBase<2^w:=(A.ordered.2.2.2.1.trans A.ordered.2.2.2.2).trans_lt space.extent
  cases query:A.query sq.1 with
  | none=>
    simpa only [«fields»,rowFields,show finProdFinEquiv.symm j=sq from rfl,query] using
      (show (Expr.lit 0).Fits w A.markerBase from trivial)
  | some p=>
    rcases p with ⟨s,q,z⟩
    by_cases allowed : finTwoEquiv sd.1=s
    · fin_cases i <;> simp only [«fields»,rowFields,show finProdFinEquiv.symm j=sq from rfl,
        query,show finProdFinEquiv.symm sq.2=sd from rfl,ite_eq_left allowed]
      all_goals first | exact A.priorView_fits _ (space.priorRow ..) room | exact A.rawView_fits _ room | exact A.shapeView_fits room
    · simp [«fields»,rowFields,show finProdFinEquiv.symm j=sq from rfl,query,show finProdFinEquiv.symm sq.2=sd from rfl,allowed,Expr.Fits]

local notation "held" => A.fields_fit boardReads prior space
local notation "mcode" => A.markerCode board (A.fields prior) held space.extent space.marker
local notation "mi" => A.markerResult board (A.fields prior) held space.extent space.marker

def program :=(A.frontCode boardReads w).seq mcode
def memory (m : Memory w) := mi (A.frontImage boardReads m)
def ticks :=A.frontClock boardReads+A.markerClock board (A.fields prior) held  space.extent space.marker

/-- The footprint and the fixed instruction tape are independent of the reached sign and occupancy bits. -/
theorem any (m : Memory w) :
    (A.program board boardReads prior space).Exec m (A.memory board boardReads prior space m) (A.ticks board boardReads prior space) ∧
    CheapCode (A.program board boardReads prior space) ∧
    ∀a,a<A.first ∨ A.endAddress≤a→A.memory board boardReads prior space m a=m a := by
  obtain ⟨a,b,c,d,e⟩:=A.ordered
  have upper:=space.extent
  let old:=A.old.image A.oldValue (fun _=>boardReads) m
  let posted:=(A.projectionBook w).output old
  have p0:=A.old.any A.oldValue (fun _=>boardReads) m (fun _ _=>space.oldRow) ((b.trans (c.trans (d.trans e))).trans_lt upper)
  have p1:=DescentContactProbeBook.run A.projectionLaw A.hosts A.groups A.batch A.projectionBase old
    ((c.trans (d.trans e)).trans_lt upper)
  have p2:=DescentContactProbePitch.installed A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase posted
    ((d.trans e).trans_lt upper)
  have p3:=A.marker_any board (A.fields prior) held space.extent space.marker (A.frontImage boardReads m)
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then p0.1 p1.1) p2.1) p3.1,cheap_seq (cheap_seq (cheap_seq p0.2.1 p1.2.1) p2.2.1) p3.2.1,?_⟩
  intro addr outside
  rcases outside with before|after
  · exact (p3.2.2 addr (.inl (before.trans_le (a.trans (b.trans c))))).trans
      ((p2.2.2.1 addr (.inl (before.trans_le (a.trans b)))).trans ((p1.2.2.2 addr (.inl (before.trans_le a))).trans (p0.2.2 addr (.inl before))))
  · exact (p3.2.2 addr (.inr after)).trans ((p2.2.2.1 addr (.inr ((d.trans e).trans after))).trans
      ((p1.2.2.2 addr (.inr ((c.trans (d.trans e)).trans after))).trans (p0.2.2 addr (.inr ((b.trans (c.trans (d.trans e))).trans after)))))

private theorem blank_source {b H G M w : ℕ} (m : Memory w) :
    Source (.lit 0) (fun (_:Fin H) (_:Fin G)=>(0:Cell b)) M m := by
  intro r
  change (0:Word w)=((data (fun (_:Fin H) (_:Fin G)=>(0:Cell b)) r).val:Word w)
  have zero : (data (fun (_:Fin H) (_:Fin G)=>(0:Cell b)) r).val=0:=by
    change (finFunctionFinEquiv (fun j:Fin M=>if _ : r.2.val*M+j.val<G then (0:Cell b) else 0)).val=0
    simp
  simp [zero]

def values (raw : Fin A.hosts→Fin A.groups→Fin A.oldFields→Cell A.fieldBits)
    (old : Bool→Fin A.half→Fin 5→Fin A.hosts→Fin A.groups→Cell A.fieldBits)
    (j : Fin A.jobs) (h : Fin (A.hosts*A.shapes)) (g : Fin A.groups) :=
  A.markerValues (fun s k f=>lifted (old s k f) h g) (fun s k f=>lifted (A.viewValue raw (A.view s k f)) h g)
    (DescentContactProbePitch.shapeField (H:=A.hosts) (S:=A.shapes) A.fieldBits h g) j

theorem sources (m : Memory w) (positive : 0<A.batch)
    (boardWidth : A.batch*max (A.fieldBits*A.oldFields) A.viewBits≤w/2)
    (raw : Fin A.hosts→Fin A.groups→Fin A.oldFields→Cell A.fieldBits)
    (old : Bool→Fin A.half→Fin 5→Fin A.hosts→Fin A.groups→Cell A.fieldBits)
    (realBoard : ∀i,Source (boardReads i) (fun h g=>raw h g i) A.batch m)
    (realOld : ∀s j f,Source (prior s j f) (old s j f) A.batch m) :
    ∀j,Source (.lookup (A.output j.val) .row) (fun h g=>A.marker board (finProdFinEquiv.symm j).1 (A.values raw old j h g))
      A.batch (A.memory board boardReads prior space m) := by
  have small:=(A.ordered.2.2.2.1.trans A.ordered.2.2.2.2).trans_lt space.extent
  obtain ⟨_,_,_,views,oldAt,shape⟩:=A.front boardReads m raw space.oldRow realBoard small positive boardWidth
  apply A.marker_sources board (A.fields prior) held space.extent space.marker (A.frontImage boardReads m) positive
    (A.values raw old)
  intro j i
  let sq:=finProdFinEquiv.symm j
  let sd:=finProdFinEquiv.symm sq.2
  cases query:A.query sq.1 with
  | none=>
    simpa only [«fields»,rowFields,values,markerValues,show finProdFinEquiv.symm j=sq from rfl,query] using
      (blank_source (b:=A.fieldBits) (H:=A.hosts*A.shapes) (G:=A.groups) (M:=A.batch) (A.frontImage boardReads m))
  | some p=>
    rcases p with ⟨s,q,z⟩
    by_cases allowed : finTwoEquiv sd.1=s
    · have donor (f : Fin 5) := oldAt (prior s sd.2 f) (old s sd.2 f) (space.priorRow s sd.2 f) (realOld s sd.2 f)
      simp only [«fields»,rowFields,values,markerValues,show finProdFinEquiv.symm j=sq from rfl,
        query,show finProdFinEquiv.symm sq.2=sd from rfl,ite_eq_left allowed]
      fin_cases i
      · exact donor 0
      · exact donor 1
      · exact views (A.view s sd.2 0)
      · exact views (A.view s sd.2 1)
      · exact donor 2
      · exact donor 3
      · exact donor 4
      · exact shape
    · simpa only [«fields»,rowFields,values,markerValues,show finProdFinEquiv.symm j=sq from rfl,
        query,show finProdFinEquiv.symm sq.2=sd from rfl,ite_eq_right allowed] using
        (blank_source (b:=A.fieldBits) (H:=A.hosts*A.shapes) (G:=A.groups) (M:=A.batch) (A.frontImage boardReads m))

end
end Hierarchy.DescentContactPreROM.Layout

end OAI
