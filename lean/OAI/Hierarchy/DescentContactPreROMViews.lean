import OAI.Hierarchy.DescentContactPreROMLayout

namespace OAI
/-! # Publishing and reusing both measured reservation fields before the public peer table -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentPackedFallbackTree.Image
open DescentFallbackPeriod.Projected DescentPackedColony.Phase.Arena
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (A : Layout)

def projectionBook (w : ℕ) :=DescentContactProbeBook.book A.projectionLaw A.hosts A.groups A.batch A.projectionBase w
def projectionMenu (j : Fin A.viewCount) :=
  ((DescentContactProbeBook.page A.projectionLaw j (fun _=>Expr.lit 0)).terms
    (DescentContactProbeBook.pageBase 1 A.viewBits A.hosts A.groups A.batch A.projectionBase j)
    A.hosts A.groups A.batch A.viewBank).menu

def projected (j : Fin A.viewCount) : Expr :=.lookup (A.projectionMenu j).dictionary (.lookup A.viewBank .row)
def priorView (x : Expr) :=
  DescentContactProbePitch.pull A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase x
def rawView (j : Fin A.viewCount) :=A.priorView (A.projected j)
def shapeView :=DescentContactProbePitch.sourceShape A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase

def frontCode (reads : Fin A.oldFields→Expr) (w : ℕ) :=
  ((A.old.code A.oldValue (fun _=>reads) w).seq (A.projectionBook w).program).seq
    (DescentContactProbePitch.code A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase w)
def frontImage (reads : Fin A.oldFields→Expr) (m : Memory w) :=
  DescentContactProbePitch.result A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase
    ((A.projectionBook w).output (A.old.image A.oldValue (fun _=>reads) m))
def frontClock (reads : Fin A.oldFields→Expr) :=
  (A.old.ticks A.oldValue (fun _=>reads)+(4+10*(A.viewCount*DescentContactProbeBook.step
    1 A.viewBits A.hosts A.groups A.batch)))+
    (4+10*DescentContactProbePitch.extent A.hosts A.shapes A.groups A.batch)

def viewValue (raw : Fin A.hosts→Fin A.groups→Fin A.oldFields→Cell A.fieldBits) (j : Fin A.viewCount)
    (v : Fin A.hosts) (g : Fin A.groups) :=(encode A.fieldBits A.viewCount).symm (A.oldValue (raw v g)) j

theorem viewValue_read (raw : Fin A.hosts→Fin A.groups→Fin A.oldFields→Cell A.fieldBits)
    (s : Bool) (lo : Fin A.half) (f : Fin 2) (v : Fin A.hosts) (g : Fin A.groups) :
    A.viewValue raw (A.view s lo f) v g=DescentReservedProbeInputs.value A.n A.residual s (D:=A.degree)
      (L:=A.lows) (cap:=A.cap) (fun k=>raw v g (DescentRotorWindowArchive.ix k)) (finProdFinEquiv.symm lo) f :=
  A.old_value_read _ _ _ _

private theorem singleton_val {a : ℕ} (x : Cell a) : (encode a 1 (fun _=>x)).val=x.val := by
  have d:=digit_encode (b:=a) (M:=1) (fun _=>x) 0
  have h : (encode a 1 (fun _=>x)).val<2^a:=by simpa using (encode a 1 (fun _=>x)).isLt
  simpa [digit,Nat.mod_eq_of_lt h] using d

private theorem data_congr {a b H G M : ℕ} (eqn : a=b) (x : Fin H→Fin G→Cell a) (y : Fin H→Fin G→Cell b)
    (same : ∀h g,(x h g).val=(y h g).val) (p : Row H G M) : (data x p).val=(data y p).val:=by
  subst b
  have xy : x=y:=funext (fun h=>funext (fun g=>Fin.ext (same h g)))
  rw [xy]

private theorem empty_fields (a n : ℕ) : (encode a n).symm 0=(fun _=>0):=by
  apply (encode a n).symm_apply_eq.mpr
  apply Fin.ext
  change 0=(finFunctionFinEquiv (fun _ : Fin n=>(0:Cell a))).val
  simp []

private theorem project_zero (j : Fin A.viewCount) : A.projectionLaw j 0=0 := by
  unfold projectionLaw
  rw [empty_fields A.viewBits 1]
  exact congrFun (empty_fields A.fieldBits A.viewCount) j

private theorem pointwise {a b H G M : ℕ} (f : Cell a→Cell b) (empty : f 0=0) (x : Fin H→Fin G→Cell a)
    (p : Row H G M) : DescentSIMDLookup.table f (data x p)=data (fun h g=>f (x h g)) p := by
  unfold DescentSIMDLookup.table data
  rw [Equiv.symm_apply_apply]
  apply congrArg (encode b M)
  funext i
  by_cases good : p.2.val*M+i.val<G <;> simp [good,empty]

private theorem front_limits : A.projectionBase≤A.pitchBase ∧ A.pitchBase≤A.markerBase :=
  ⟨A.ordered.2.1,A.ordered.2.2.1⟩

private theorem dictionary_fits (j : Fin A.viewCount) (room : A.pitchBase<2^w) :
    (A.projectionMenu j).dictionary.Fits w A.pitchBase := by
  let t:=DescentContactProbeBook.page A.projectionLaw j (fun _=>Expr.lit 0)
  let base:=DescentContactProbeBook.pageBase 1 A.viewBits A.hosts A.groups A.batch A.projectionBase j
  have ending:=DescentContactProbeBook.page_end A.projectionLaw A.hosts A.groups A.batch A.projectionBase j (fun _=>Expr.lit 0)
  have bound:=Nat.add_le_add_left (Nat.mul_le_mul_right (DescentContactProbeBook.step 1 A.viewBits A.hosts A.groups A.batch) j.isLt) A.projectionBase
  have last : t.stop base A.hosts A.groups A.batch≤A.pitchBase := calc
    _≤t.stop base A.hosts A.groups A.batch+1:=Nat.le_succ _
    _=_:=ending
    _≤A.pitchBase:=bound
  have finish : (A.projectionMenu j).dictionary.base+(A.projectionMenu j).dictionary.size≤A.pitchBase:=
    (Nat.le_add_right ..).trans last
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (finish.trans_lt room),finish⟩

theorem projected_fits (j : Fin A.viewCount) (room : A.pitchBase<2^w) : (A.projected j).Fits w A.pitchBase := by
  have oldOK:=A.old.output_fits (N:=A.oldFields) (field:=A.fieldBits) 0 (by decide : 0<1)
    (A.front_limits.1.trans_lt room)
  exact ⟨A.dictionary_fits j room,⟨oldOK.1,oldOK.2.1,oldOK.2.2.trans A.front_limits.1⟩,trivial⟩

theorem rawView_fits (j : Fin A.viewCount) (room : A.markerBase<2^w) : (A.rawView j).Fits w A.markerBase :=
  DescentContactProbePitch.fits_pull _ _ _ _ _ _ _ (A.projected_fits j (A.front_limits.2.trans_lt room)) room

theorem priorView_fits (x : Expr) (held : x.Fits w A.first) (room : A.markerBase<2^w) :
    (A.priorView x).Fits w A.markerBase :=
  DescentContactProbePitch.fits_pull _ _ _ _ _ _ _ (ProtocolRAMGeneratedWrite.fits_mono _ (A.ordered.1.trans A.front_limits.1) held) room

theorem shapeView_fits (room : A.markerBase<2^w) : A.shapeView.Fits w A.markerBase :=
  ⟨DescentContactProbePitch.table_fits _ _ _ _ _ _ room 1,trivial⟩

private theorem projection_source (j : Fin A.viewCount) (mem : Memory w) (room : A.pitchBase<2^w)
    (raw : Fin A.hosts→Fin A.groups→Fin A.oldFields→Cell A.fieldBits)
    (booked : (A.projectionBook w).Resident mem)
    (view : Source (.lookup A.viewBank .row) (fun h g=>A.oldValue (raw h g)) A.batch mem) :
    Source (A.projected j) (A.viewValue raw j) A.batch mem := by
  intro p
  let encoded:=fun (h : Fin A.hosts) (g : Fin A.groups)=>encode A.viewBits 1 (fun _=>A.oldValue (raw h g))
  have same :=data_congr (Nat.mul_one A.viewBits) encoded (fun h g=>A.oldValue (raw h g))
    (fun h g=>singleton_val _) p
  have key : (.lookup A.viewBank .row : Expr).eval mem ((row A.hosts A.groups A.batch p).val:Word w)=
      ((data encoded p).val:Word w):=(view p).trans (congrArg (fun n : ℕ=>(n:Word w)) same.symm)
  have legal : (data encoded p).val<(A.projectionMenu j).dictionary.size:=(data encoded p).isLt
  have resident:=DescentContactProbeBook.fixed A.projectionLaw A.hosts A.groups A.batch A.projectionBase
    mem booked room j (fun _=>Expr.lit 0) A.viewBank
  change (A.projectionMenu j).dictionary.read mem ((Expr.lookup A.viewBank .row).eval _ _)=_
  rw [key,bank_read _ _ legal (A.dictionary_fits j room)]
  refine (resident.2.1 (data encoded p)).trans ?_
  change ((DescentSIMDLookup.table (A.projectionLaw j) (data encoded p)).val:Word w)=_
  rw [pointwise _ (A.project_zero j)]
  simp only [encoded,projection_encoded]
  rfl

theorem front (reads : Fin A.oldFields→Expr) (mem : Memory w)
    (raw : Fin A.hosts→Fin A.groups→Fin A.oldFields→Cell A.fieldBits)
    (held : ∀i,(reads i).Fits w A.first)
    (prior : ∀i,Source (reads i) (fun v g=>raw v g i) A.batch mem)
    (room : A.markerBase<2^w) (batchPos : 0<A.batch)
    (packed : A.batch*max (A.fieldBits*A.oldFields) A.viewBits≤w/2) :
    let dst:=A.frontImage reads mem
    (A.frontCode reads w).Exec mem dst (A.frontClock reads) ∧ CheapCode (A.frontCode reads w) ∧
    (∀addr,addr<A.first ∨ A.markerBase≤addr→dst addr=mem addr) ∧
    (∀j,Source (A.rawView j) (DescentContactProbePitch.lift (S:=A.shapes) (A.viewValue raw j)) A.batch dst) ∧
    (∀(x : Expr) (values : Fin A.hosts→Fin A.groups→Cell A.fieldBits),x.Fits w A.first→Source x values A.batch mem→
      Source (A.priorView x) (DescentContactProbePitch.lift (S:=A.shapes) values) A.batch dst) ∧
    Source A.shapeView (DescentContactProbePitch.shapeField (H:=A.hosts) (S:=A.shapes) (G:=A.groups) A.fieldBits) A.batch dst := by
  intro dst
  let r:=fun _ : ℕ=>reads
  let old:=A.old.image A.oldValue r mem
  let book:=A.projectionBook w
  let mid:=book.output old
  have opRoom:=A.front_limits.2.trans_lt room
  have oldRoom:=A.front_limits.1.trans_lt opRoom
  obtain ⟨exec0,cheap0,frame0⟩:=A.old.any A.oldValue r mem (fun _ _ j=>held j) oldRoom
  obtain ⟨exec1,cheap1,books,frame1⟩:=DescentContactProbeBook.run A.projectionLaw A.hosts A.groups A.batch
    A.projectionBase old opRoom
  obtain ⟨exec2,cheap2,frame2,_⟩:=DescentContactProbePitch.installed A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase mid room
  have oldSource:=A.old.words A.oldValue r mem (fun _ _ j=>held j) oldRoom batchPos packed (fun _=>raw)
    (fun _ _ j=>prior j) 0 (by decide : 0<1)
  have oldFit:=A.old.output_fits (N:=A.oldFields) (field:=A.fieldBits) 0 (by decide : 0<1) oldRoom
  have view : Source (.lookup A.viewBank .row) (fun h g=>A.oldValue (raw h g)) A.batch mid :=fun p=>
    (eval_below _ _ old mid (show (.lookup A.viewBank .row : Expr).Fits w A.projectionBase from ⟨oldFit,trivial⟩)
      (fun z hz=>frame1 z (.inl hz))).trans (oldSource p)
  refine ⟨Procedure.Exec.then (Procedure.Exec.then exec0 exec1) exec2,cheap_seq (cheap_seq cheap0 cheap1) cheap2,?_,?_,?_,?_⟩
  · intro addr outside
    rcases outside with small|large
    · exact (frame2 addr (.inl (small.trans_le (A.ordered.1.trans A.front_limits.1)))).trans
        ((frame1 addr (.inl (small.trans_le A.ordered.1))).trans (frame0 addr (.inl small)))
    · exact (frame2 addr (.inr large)).trans ((frame1 addr (.inr (A.front_limits.2.trans large))).trans
        (frame0 addr (.inr ((A.front_limits.1.trans A.front_limits.2).trans large))))
  · intro j
    exact DescentContactProbePitch.source_pull _ _ mid room _ _ (A.projected_fits j opRoom)
      (A.projection_source j mid opRoom raw books view)
  · intro x values hx before
    apply DescentContactProbePitch.source_pull _ _ mid room x values
      (ProtocolRAMGeneratedWrite.fits_mono _ (A.ordered.1.trans A.front_limits.1) hx)
    exact fun p=>(eval_below _ _ mem mid hx (fun z hz=>
      (frame1 z (.inl (hz.trans_le A.ordered.1))).trans (frame0 z (.inl hz)))).trans (before p)
  · exact DescentContactProbePitch.shape_source _ _ mid room

end
end Hierarchy.DescentContactPreROM.Layout

end OAI
