import OAI.Hierarchy.DescentContactPreROM

namespace OAI
/-! # Clock and static instruction names for the full prior-to-marker publication -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentPackedColony.Phase.Arena
open DescentPacking.PackedMatch.Local.Gather DescentSixParty.Chronology DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable (A : Layout) {ports w : ℕ} (board : NonlinearExpanders.Graph A.n ports)
variable (boardReads : Fin A.oldFields→Expr) (prior : Bool→Fin A.half→Fin 5→Expr)
variable (space : A.Space boardReads prior w)
local notation "R" => A.rows
local notation "K" => A.sockets

def oldWork := (A.old.op A.oldValue (fun _=>boardReads) 0).work
def fieldWork (j : Fin A.jobs) :=
  let t:=A.termPage board (finProdFinEquiv.symm j).1 (A.fields prior j) j
  (assembly t.tables (A.fields prior j)).work

private theorem assemble_bound {n : ℕ} (ts : Fin n→Tables) (xs : Fin n→Expr) (lim : ℕ)
    (each : ∀i,(xs i).work≤lim) : (assembly ts xs).work≤1+n*(lim+11) := by
  have aux (is : List (Fin n)) : (collect ts xs is).work≤1+is.length*(lim+11):=by
    induction is with
    | nil=>simp [collect];rfl
    | cons i is ih=>
      have hi:=each i
      simp only [collect,DescentPackedZip.work,List.length_cons,Nat.succ_mul] at *
      omega
  simpa only [assembly,List.length_finRange] using aux (List.finRange n)

def oldLimit (width : ℕ) := 1+A.oldFields*(width+11)
def markerLimit (width : ℕ) := 1+8*(max (8*width) 96+11)

theorem old_work_le (lim : ℕ) (each : ∀i,(boardReads i).work≤lim) :
    A.oldWork boardReads≤A.oldLimit lim := assemble_bound _ _ _ each

theorem marker_work_le (lim : ℕ) (each : ∀s j i,(prior s j i).work≤lim) (j : Fin A.jobs) :
    A.fieldWork board prior j≤ markerLimit lim := by
  apply assemble_bound
  let sq:=finProdFinEquiv.symm j
  let sd:=finProdFinEquiv.symm sq.2
  have previous (s k f) : (A.priorView (prior s k f)).work≤ max (8*lim) 96:=by
    have sub:=ProtocolRAM.Calendar.CatalogueRows.substitute_work (prior s k f)
      (DescentContactProbePitch.value A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase 0)
    change (A.priorView (prior s k f)).work≤(prior s k f).work*8 at sub
    exact (sub.trans (Nat.mul_le_mul_right 8 (each s k f))).trans (by rw [Nat.mul_comm lim];exact le_max_left _ _)
  have measured (k : Fin A.viewCount) : (A.rawView k).work≤ max (8*lim) 96:=by
    have sub:=ProtocolRAM.Calendar.CatalogueRows.substitute_work (A.projected k)
      (DescentContactProbePitch.value A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase 0)
    exact sub.trans (show 96≤ max (8*lim) 96 from le_max_right _ _)
  have shape : A.shapeView.work≤ max (8*lim) 96:=(by decide : 7≤96).trans (le_max_right ..)
  have blank : (Expr.lit 0).work≤ max (8*lim) 96:=(by decide : 1≤96).trans (le_max_right ..)
  intro i
  cases query:A.query sq.1 with
  | none=>simpa only [Layout.fields,rowFields,show finProdFinEquiv.symm j=sq from rfl,query] using blank
  | some k=>
    rcases k with ⟨s,q,z⟩
    by_cases hit : finTwoEquiv sd.1=s
    · fin_cases i <;> simp only [Layout.fields,rowFields,show finProdFinEquiv.symm j=sq from rfl,
        query,show finProdFinEquiv.symm sq.2=sd from rfl,ite_eq_left hit]
      all_goals first | exact previous .. | exact measured .. | exact shape
    · simpa only [Layout.fields,rowFields,show finProdFinEquiv.symm j=sq from rfl,query,
        show finProdFinEquiv.symm sq.2=sd from rfl,ite_eq_right hit] using blank

def staticLength:=A.viewCount*DescentContactProbeBook.step 1 A.viewBits A.hosts A.groups A.batch+
    DescentContactProbePitch.extent A.hosts A.shapes A.groups A.batch+
    A.sockets*DescentContactProbeBook.step 8 A.fieldBits (A.hosts*A.shapes) A.groups A.batch

def clockBound (oldLimit markerLimit : ℕ) :=
  A.old.costBound A.oldFields A.fieldBits oldLimit+(12+10*A.staticLength)+
    (4+A.jobs*(4+R*(2*markerLimit+4)+(4+44*R)))

def size (oldLimit markerLimit : ℕ) :=
  A.old.nameBound A.oldFields A.fieldBits oldLimit+15*(A.staticLength+3)+
    (15+A.jobs*(102+4*markerLimit))

private theorem names_series (ps : List (Shelf w)) :
    names (Shelf.series ps).program=(ps.map (fun (p : Shelf w)=>DescentStaticWordColumn.names p.program)).sum+15 := by
  induction ps with
  | nil=>change names (scan w 0 0 (.lit 0))=15;rw [names_scan];rfl
  | cons p ps ih=>
    change names (p.program.seq (Shelf.series ps).program)=_
    rw [names_seq,ih]
    simp [Nat.add_assoc]

private theorem job_names (j : Fin A.jobs) :
    names (A.markerJob board (A.fields prior) (A.fields_fit boardReads prior space) space.extent space.marker j).program=
      102+4*A.fieldWork board prior j := by
  change names ((scan w _ _ (assembly _ _)).seq (scan w _ _ (DescentSIMDLookup.lookup _)))=_
  simp [names_seq,names_scan,lookup_work,fieldWork]
  omega

private theorem job_clock (j : Fin A.jobs) :
    (A.markerJob board (A.fields prior) (A.fields_fit boardReads prior space) space.extent space.marker j).ticks=
        4+R*(2*A.fieldWork board prior j+4)+(4+44*R) := by
  change (4+R*(2*(assembly _ _).work+4))+(4+R*(2*(DescentSIMDLookup.lookup _).work+4))=_
  simp [lookup_work,fieldWork,Nat.mul_comm 44]

theorem priced (oldLimit markerLimit : ℕ) (pre : A.oldWork boardReads≤oldLimit)
    (post : ∀j,A.fieldWork board prior j≤ markerLimit) :
    A.ticks board boardReads prior space≤A.clockBound oldLimit markerLimit ∧
    names (A.program board boardReads prior space)≤A.size oldLimit markerLimit := by
  let jobs:=A.markerJob board (A.fields prior) (A.fields_fit boardReads prior space) space.extent space.marker
  have hw (j : ℕ) (_ : j<A.old.jobs) : (A.old.op A.oldValue (fun _=>boardReads) j).work≤oldLimit:=pre
  have bounds:=A.old.priced (w:=w) A.oldValue (fun _=>boardReads) oldLimit hw
  have tc : (∑j,(jobs j).ticks)≤A.jobs*(4+R*(2*markerLimit+4)+(4+44*R)):=by
    calc
      _ ≤ ∑_ : Fin A.jobs,(4+R*(2*markerLimit+4)+(4+44*R)):=Finset.sum_le_sum (fun j _=>by
        rw [show (jobs j).ticks=_ from A.job_clock board boardReads prior space j];gcongr; exact post j)
      _ = _:=by simp
  have ns : (∑j,names (jobs j).program)≤A.jobs*(102+4*markerLimit):=by
    calc
      _ ≤ ∑_ : Fin A.jobs,(102+4*markerLimit) :=Finset.sum_le_sum (fun j _=>by
        rw [show names (jobs j).program=_ from A.job_names board boardReads prior space j];gcongr; exact post j)
      _ = _:=by simp
  have series : names (Shelf.series (Shelf.catalog jobs)).program=(∑j,names (jobs j).program)+15:=by
    rw [names_series,Shelf.catalog,List.map_reverse,List.sum_reverse,List.map_ofFn,List.sum_ofFn]
    rfl
  have projection:=(A.projectionBook w).hardware.2
  have markers:=(A.markerImage (w:=w) board).hardware.2
  have views : (A.projectionBook w).length=A.viewCount*DescentContactProbeBook.step 1 A.viewBits A.hosts A.groups A.batch:=Nat.add_sub_cancel_left ..
  have marked : (A.markerImage (w:=w) board).length=A.sockets*DescentContactProbeBook.step 8 A.fieldBits
        (A.hosts*A.shapes) A.groups A.batch:=Nat.add_sub_cancel_left ..
  have pitch : names (DescentContactProbePitch.code A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase w)=
      15*(DescentContactProbePitch.extent A.hosts A.shapes A.groups A.batch+1):=names_mount ..
  rw [views] at projection;rw [marked] at markers
  constructor
  · unfold ticks frontClock markerClock clockBound staticLength
    change _+(_+((∑j,(jobs j).ticks)+4))≤_
    omega
  · unfold program frontCode markerCode size staticLength
    simp only [names_seq,projection,markers,pitch]
    change _+(_+names (Shelf.series (Shelf.catalog jobs)).program)≤_
    rw [series]
    omega

theorem reads_priced (oldWidth priorWidth : ℕ) (inputs : ∀i,(boardReads i).work≤oldWidth)
    (sensors : ∀s k f,(prior s k f).work≤priorWidth) :
    A.ticks board boardReads prior space≤A.clockBound (A.oldLimit oldWidth) (markerLimit priorWidth) ∧
    names (A.program board boardReads prior space)≤A.size (A.oldLimit oldWidth) (markerLimit priorWidth) :=
  A.priced board boardReads prior space _ _ (A.old_work_le boardReads _ inputs)
    (A.marker_work_le board prior _ sensors)

end
end Hierarchy.DescentContactPreROM.Layout

end OAI
