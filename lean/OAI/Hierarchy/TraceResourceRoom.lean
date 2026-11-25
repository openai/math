import OAI.Hierarchy.TraceResourcePublisher

namespace OAI
/-! # Word-room conditions for the fixed registration scans -/
namespace Hierarchy.TraceAdmission.Resources
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalPinsExpr
open scoped Classical Fin.CommRing

/-- The scratch and public output windows come after all immutable numeric
sources. Each relevant mixed-radix product fits in one physical word. -/
structure Room (W ctrl header : ℕ) (p : Parameters ℕ) : Prop where
  control : ctrl<p.scratch
  header : header+16≤p.scratch
  heads : p.heads+p.roots≤p.scratch
  links : p.links+p.lanes≤p.scratch
  costs : p.charges+2*(p.firstFinal+p.roots)≤p.scratch
  scratch : p.scratch+(p.lanes+1)*(p.directions+1)≤p.resources
  space : p.resources+p.roots*(p.directions+2)<2^W
  dimensions : p.directions+2<2^W
  bits : 2*((p.lanes+1)*p.pairSpan)<2^W
  bands : (p.directions+1)*p.band<2^W
  cap : p.cap<2^W

private theorem scratch_offset {lanes stride q col : ℕ} (row : q≤lanes) (column : col<stride) :
    q*stride+col<(lanes+1)*stride := calc
  _ < q*stride+stride := Nat.add_lt_add_left column _
  _ = (q+1)*stride := (Nat.succ_mul q stride).symm
  _ ≤ _ := Nat.mul_le_mul_right stride (Nat.succ_le_succ row)

/-- The shape is read from the issuing header, including its two generated windows. -/
structure Header {W : ℕ} (ctrl header : ℕ) (p : Parameters ℕ) (m : Memory W) : Prop where
  pointer : (m ctrl).val=header
  scratch : (m header).val=p.scratch
  slength : (m (header+1)).val=(p.lanes+1)*(p.directions+1)
  resource : (m (header+2)).val=p.resources
  rlength : (m (header+3)).val=p.roots*(p.directions+2)
  params : ∀ i : Fin 12, (m (header+4+i.val)).val=
    ![p.lanes,p.roots,p.directions,p.pairSpan,p.band,p.cap,p.heads,p.links,p.scratch,p.resources,p.charges,p.firstFinal] i

private theorem fields_eval {W : ℕ} (ctrl header : ℕ) (p : Parameters ℕ) (m : Memory W)
    (h : Header ctrl header p m) (a : ℕ) :
    (fields ctrl).map (natEval W (fun z=>(m z).val) a)=p := by
  cases p with
  | mk lanes roots dirs pairSpan band cap heads links scratch resources charges first =>
    simp only [fields,Parameters.map,natEval,Formula.natural,natOp,h.pointer]
    congr 1
    all_goals first
      | simpa +arith using h.params 0 | simpa +arith using h.params 1
      | simpa +arith using h.params 2 | simpa +arith using h.params 3
      | simpa +arith using h.params 4 | simpa +arith using h.params 5
      | simpa +arith using h.params 6 | simpa +arith using h.params 7
      | simpa +arith using h.params 8 | simpa +arith using h.params 9
      | simpa +arith using h.params 10 | simpa +arith using h.params 11

private theorem fields_before {W : ℕ} {ctrl header : ℕ} {p : Parameters ℕ} {m o : Memory W}
    (room : Room W ctrl header p) (H : Header ctrl header p m)
    (frame : ∀ z<p.scratch,o z=m z) : Header ctrl header p o := by
  refine ⟨by rw [frame _ room.control,H.pointer],?_,?_,?_,?_,?_⟩
  all_goals have := room.header
  · rw [frame _ (by omega),H.scratch]
  · rw [frame _ (by omega),H.slength]
  · rw [frame _ (by omega),H.resource]
  · rw [frame _ (by omega),H.rlength]
  · intro i
    rw [frame _ (by have := i.isLt; omega),H.params]

/-- Every numeric expression used for output publication is bounded by the actual
array extent. The successor number is read only from the physical head table. -/
theorem resource_fits {W ctrl header : ℕ} (p : Parameters ℕ) (room : Room W ctrl header p)
    (m : Memory W) (H : Header ctrl header p m) (i : ℕ) (active : i<p.roots*(p.directions+2))
    (headBound : ∀ v<p.roots,(m (p.heads+v)).val≤p.lanes) :
    (resourceExpr (fields ctrl)).Fits W (fun _=>0) (fun z=>(m z).val) (fun _=>p.resources+i) := by
  let raw := fun z=>(m z).val
  let vs := fun _ : Fin 1=>p.resources+i
  let ev := natEval W raw (p.resources+i)
  let fit := Formula.Fits W (fun _=>0) raw vs
  have b := room.space
  have s := room.scratch
  have small := room.dimensions
  have ht := room.header
  have ptr : raw ctrl=header := H.pointer
  have ctrlWord : ctrl<2^W := by have := room.control;omega
  have fieldsFit (j : ℕ) (hj : j≤15) :
      fit (.load (.op .add (.load (.lit ctrl)) (.lit j))) :=
    ⟨⟨⟨trivial,ctrlWord⟩,trivial,trivial⟩,by change raw ctrl+j<2^W;rw [ptr];omega⟩
  let P := fields ctrl
  have pe : P.map ev=p := fields_eval _ _ _ _ H _
  have re : ev P.resources=p.resources := congrArg Parameters.resources pe
  have di : ev P.directions=p.directions := congrArg Parameters.directions pe
  have hd : ev P.heads=p.heads := congrArg Parameters.heads pe
  have ch : ev P.charges=p.charges := congrArg Parameters.charges pe
  have fi : ev P.firstFinal=p.firstFinal := congrArg Parameters.firstFinal pe
  have sc : ev P.scratch=p.scratch := congrArg Parameters.scratch pe
  have la : ev P.lanes=p.lanes := congrArg Parameters.lanes pe
  let v:=i/(p.directions+2)
  let col:=i%(p.directions+2)
  have hv : v<p.roots := (Nat.div_lt_iff_lt_mul (by omega)).mpr active
  have hcol : col<p.directions+2 := Nat.mod_lt _ (by omega)
  have hhead : p.heads+v<2^W := by have := room.heads;omega
  have colWord : col<2^W := hcol.trans small
  have headWord : raw (p.heads+v)<2^W := (m (p.heads+v)).isLt
  have hb : raw (p.heads+v)≤p.lanes := headBound v hv
  let h := ptrRow p.lanes (raw (p.heads+v))
  have hr : h≤p.lanes := by unfold h ptrRow;split <;> omega
  have cost : p.charges+2*(p.firstFinal+v)<2^W := by have := room.costs;omega
  have cell : p.scratch+h*(p.directions+1)+(col-1)<2^W := by
    have upper := scratch_offset hr (show col-1<p.directions+1 by omega)
    omega
  have lanesW : p.lanes+1<2^W := by
    have le : p.lanes+1≤(p.lanes+1)*(p.directions+1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hr0 : fit P.resources := fieldsFit 13 (by decide)
  have hd0 : fit P.directions := fieldsFit 6 (by decide)
  have hh0 : fit P.heads := fieldsFit 10 (by decide)
  have hc0 : fit P.charges := fieldsFit 14 (by decide)
  have hf0 : fit P.firstFinal := fieldsFit 15 (by decide)
  have hs0 : fit P.scratch := fieldsFit 12 (by decide)
  have hl0 : fit P.lanes := fieldsFit 4 (by decide)
  change fit (resourceExpr P)
  unfold resourceExpr
  simp only [fit,ev,natEval,vs] at hr0 hd0 hh0 hc0 hf0 hs0 hl0 re di hd ch fi sc la ⊢
  simp only [pointerRow,Formula.Fits,Formula.natural,natOp,opFits,natTest,
    re,di,hd,ch,fi,sc,la,hr0,hd0,hh0,hc0,hf0,hs0,hl0,true_and,decide_eq_true_eq,
    Nat.add_sub_cancel_left]
  clear pe re di hd ch fi sc la hr0 hd0 hh0 hc0 hf0 hs0 hl0
  have addressWord : p.resources+i<2^W := by omega
  have regWord : i<2^W := by omega
  dsimp only [v,col,h,ptrRow] at cost cell hhead hb hcol headWord colWord
  split_ifs at cell ⊢ <;> (try simp only [Nat.zero_mul,Nat.add_zero] at *) <;>
    (repeat' apply And.intro) <;> first | assumption | exact True.intro | (try omega)

/-- The first scan can address every list successor and clamp the public
pair/intake intervals with ordinary natural arithmetic at the selected word width. -/
theorem scratch_fits {W ctrl header : ℕ} (p : Parameters ℕ) (room : Room W ctrl header p)
    (m : Memory W) (H : Header ctrl header p m) (i : ℕ)
    (active : i<(p.lanes+1)*(p.directions+1)) :
    (scratchExpr (fields ctrl)).Fits W (fun _=>0) (fun z=>(m z).val) (fun _=>p.scratch+i) := by
  let raw := fun z=>(m z).val
  let vs := fun _ : Fin 1=>p.scratch+i
  let ev := natEval W raw (p.scratch+i)
  let fit := Formula.Fits W (fun _=>0) raw vs
  let P := fields ctrl
  have pe : P.map ev=p := fields_eval _ _ _ _ H _
  have re : ev P.scratch=p.scratch := congrArg Parameters.scratch pe
  have di : ev P.directions=p.directions := congrArg Parameters.directions pe
  have ln : ev P.links=p.links := congrArg Parameters.links pe
  have la : ev P.lanes=p.lanes := congrArg Parameters.lanes pe
  have sp : ev P.pairSpan=p.pairSpan := congrArg Parameters.pairSpan pe
  have band : ev P.band=p.band := congrArg Parameters.band pe
  have cap : ev P.cap=p.cap := congrArg Parameters.cap pe
  have space := room.space
  have scratch := room.scratch
  have bits := room.bits
  have bands := room.bands
  have limits := room.dimensions
  have hdr := room.header
  have capW := room.cap
  have ptr : raw ctrl=header := H.pointer
  have cw : ctrl<2^W := by have := room.control;omega
  have fieldsFit (j : ℕ) (hj : j≤15) :
      fit (.load (.op .add (.load (.lit ctrl)) (.lit j))) :=
    ⟨⟨⟨trivial,cw⟩,trivial,trivial⟩,by change raw ctrl+j<2^W;rw [ptr];omega⟩
  have fr : fit P.scratch := fieldsFit 12 (by decide)
  have fd : fit P.directions := fieldsFit 6 (by decide)
  have fl : fit P.links := fieldsFit 11 (by decide)
  have fa : fit P.lanes := fieldsFit 4 (by decide)
  have fs : fit P.pairSpan := fieldsFit 7 (by decide)
  have fb : fit P.band := fieldsFit 8 (by decide)
  have fc : fit P.cap := fieldsFit 9 (by decide)
  let r := i/(p.directions+1)
  let col := i%(p.directions+1)
  let q := p.lanes-r
  have enough : 0<p.directions+1 := by omega
  have hrow : r<p.lanes+1 := (Nat.div_lt_iff_lt_mul enough).mpr active
  have hcol : col<p.directions+1 := Nat.mod_lt _ enough
  have lane := Nat.le_mul_of_pos_right (p.lanes+1) enough
  have point : p.scratch+i<2^W := by omega
  have qle : q≤p.lanes := Nat.sub_le ..
  have addressRoom : p.resources<2^W := (Nat.le_add_right ..).trans_lt space
  have lanesRoom : p.lanes+1<2^W := (lane.trans ((Nat.le_add_left ..).trans scratch)).trans_lt addressRoom
  have rowRoom : r<2^W := hrow.trans lanesRoom
  have colRoom : col<2^W := hcol.trans (by omega)
  have product : q*p.pairSpan+p.pairSpan≤(p.lanes+1)*p.pairSpan := by
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.succ_le_succ qle)
  have spanRoom : 2*p.pairSpan<2^W := by omega
  have loRoom : 2*(q*p.pairSpan)<2^W := by omega
  have hiRoom : q*p.pairSpan+p.pairSpan<2^W := by omega
  have rightRoom : col*p.band<2^W := (Nat.mul_le_mul_right p.band hcol.le).trans_lt bands
  have leftRoom : (col-1)*p.band<2^W := (Nat.mul_le_mul_right p.band (Nat.sub_le col 1)).trans_lt rightRoom
  have link : p.links+q<2^W := by have := room.links;omega
  have received : raw (p.links+q)<2^W := (m _).isLt
  let tail := ptrRow p.lanes (raw (p.links+q))
  have ht : tail≤p.lanes := by dsimp [tail,ptrRow];split <;> omega
  have addr : p.scratch+tail*(p.directions+1)+col<2^W := calc
    _ < p.scratch+(tail+1)*(p.directions+1) := by rw [Nat.add_mul,Nat.one_mul];omega
    _ ≤ p.scratch+(p.lanes+1)*(p.directions+1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_succ ht)) _
    _ ≤ p.resources := scratch
    _ < 2^W := addressRoom
  change fit (scratchExpr P)
  unfold scratchExpr
  simp only [fit,ev,natEval,vs] at fr fd fl fa fs fb fc re di ln la sp cap band ⊢
  simp only [pointerRow,Formula.Fits,Formula.natural,natOp,opFits,natTest,
    fr,fd,fl,fa,fs,fb,fc,re,di,ln,la,sp,band,cap,true_and,decide_eq_true_eq,
    Nat.add_sub_cancel_left]
  clear pe re di ln la sp cap band fr fd fl fa fs fb fc
  dsimp only [q,r,col,tail,ptrRow] at product spanRoom loRoom hiRoom rightRoom leftRoom link received addr hrow hcol rowRoom colRoom
  split_ifs at addr ⊢ <;> (repeat' constructor) <;> omega

private theorem headerWord_at {W ctrl header : ℕ} {p : Parameters ℕ} {m : Memory W}
    (r : Room W ctrl header p) (H : Header ctrl header p m) (j : ℕ) (hj : j≤15) :
    HeaderScan.headerWord m (ctrl:Word W) j = m (header+j) := by
  have space := r.space
  have l := r.scratch
  have h := r.header
  have ctrlFit : ctrl<2^W := by have := r.control;omega
  have equ : m ctrl=(header:Word W) := by rw [←H.pointer,Fin.cast_val_eq_self]
  unfold HeaderScan.headerWord
  rw [Fin.val_cast_of_lt ctrlFit,equ,←Nat.cast_add,Fin.val_cast_of_lt (show header+j<2^W by omega)]

def scratchLength (p : Parameters ℕ) := (p.lanes+1)*(p.directions+1)
def resourceLength (p : Parameters ℕ) := p.roots*(p.directions+2)

def intermediate {W : ℕ} (p : Parameters ℕ) (m : Memory W) :=
  fillSegment p.scratch (scratchLength p) (scratchWord p m) m

def completed {W : ℕ} (p : Parameters ℕ) (m : Memory W) :=
  let tmp:=intermediate p m
  fillSegment p.resources (resourceLength p)
    (fun a=>(resourceValue p (fun z=>(tmp z).val) a : Word W)) tmp

private theorem immutable_small {W : ℕ} {p : Parameters ℕ} (m : Memory W) (n z : ℕ) (h : z<p.scratch) :
    fillSegment p.scratch n (scratchWord p m) m z=m z := by
  simp [fillSegment,Nat.not_le_of_lt h]

/-- After publication, every resource row lies in the single bank consumed by
the allocator. The only input-dependent hypotheses describe the actual sorted
linked lists and the original memory header. -/
theorem publish {W ctrl header : ℕ} (p : Parameters ℕ) (r : Room W ctrl header p)
    (m old : Memory W) (H : Header ctrl header p m) (dest : Fin p.lanes→Fin p.roots)
    (lists : TraceIntervalScanner.Output p.heads p.links dest old m) :
    ((scratchPass W ctrl).seq (resourcePass W ctrl)).Spec (·=m)
      (fun _ o=>o=completed p m) (ticks ctrl p) := by
  have sp := r.space
  have sl := r.scratch
  have low := r.links
  have hs : p.scratch+scratchLength p<2^W := sl.trans_lt (by omega)
  let tmp := intermediate p m
  have preserve (a : ℕ) (ha : a<p.scratch) : tmp a=m a :=
    immutable_small m _ a ha
  have htmp : Header ctrl header p tmp := fields_before r H preserve
  have linked (i : ℕ) (hi : i<p.lanes) :
      (m (p.links+i)).val=0 ∨ i+1<(m (p.links+i)).val ∧ (m (p.links+i)).val≤p.lanes :=
    lists.link_monotone ⟨i,hi⟩
  have first : (scratchPass W ctrl).Spec (·=m) (fun _ o=>o=tmp)
      (11+scratchLength p*(2*(scratchExpr (fields ctrl)).work+4)) :=
    scratchPass_spec ctrl p m (scratchLength p) hs
      (by rw [headerWord_at r H 0 (by decide),Nat.add_zero,H.scratch])
      (by rw [headerWord_at r H 1 (by decide),H.slength]; rfl)
      (scratchWord p m) (by
        intro i hi
        let mid := fillSegment p.scratch i (scratchWord p m) m
        have same (z : ℕ) (hz : z<p.scratch) : mid z=m z := immutable_small m _ z hz
        have hdr : Header ctrl header p mid := fields_before r H same
        exact ⟨scratch_fits p r mid hdr i hi,fields_eval _ _ _ _ hdr _,
          scratchWord_step p m low linked i hi⟩)
  let words := fun a=>(resourceValue p (fun z=>(tmp z).val) a : Word W)
  have second : (resourcePass W ctrl).Spec (·=tmp) (fun _ o=>o=completed p m)
      (11+resourceLength p*(2*(resourceExpr (fields ctrl)).work+4)) :=
    resourcePass_spec ctrl p tmp (resourceLength p) r.space
      (by rw [headerWord_at r htmp 2 (by decide),htmp.resource])
      (by rw [headerWord_at r htmp 3 (by decide),htmp.rlength];rfl)
      words (by
        intro i hi
        let mid := fillSegment p.resources i words tmp
        have before (z : ℕ) (hz : z<p.resources) : mid z=tmp z := by
          simp [mid,fillSegment,Nat.not_le_of_lt hz]
        have hdr : Header ctrl header p mid :=
          fields_before r htmp (fun z hz=>before _ (by omega))
        have heads (v : ℕ) (hv : v<p.roots) : (mid (p.heads+v)).val≤p.lanes := by
          have low : p.heads+v<p.scratch := by have := r.heads;omega
          rw [before _ (by omega),preserve _ low]
          exact lists.head_bound ⟨v,hv⟩
        refine ⟨resource_fits p r mid hdr _ hi heads,fields_eval _ _ _ _ hdr _,?_⟩
        let stride:=p.directions+2
        let v:=i/stride
        let col:=i%stride
        have hv : v<p.roots := (Nat.div_lt_iff_lt_mul (by dsimp [stride];omega)).mpr hi
        have hc : col<stride := Nat.mod_lt _ (by dsimp [stride];omega)
        have parts : p.resources+i=p.resources+v*(p.directions+2)+col := by
          have e := Nat.mod_add_div i stride
          rw [Nat.mul_comm stride (i/stride)] at e
          dsimp only [col,v,stride] at e ⊢
          omega
        change (resourceValue p (fun z=>(mid z).val) (p.resources+i):Word W) = words _
        change _=(resourceValue p (fun z=>(tmp z).val) (p.resources+i):Word W)
        rw [parts,resource_index _ _ _ _ hc,resource_index _ _ _ _ hc]
        by_cases zero : col=0
        · simp only [ite_eq_left zero]
          rw [before _ (by have b:=r.costs;omega)]
        · have low : p.heads+v<p.resources := by have x:=r.heads;omega
          simp only [ite_eq_right zero,before _ low]
          let q := ptrRow p.lanes (tmp (p.heads+v)).val
          have hq : q≤p.lanes := by dsimp [q,ptrRow];split <;>omega
          have offset := scratch_offset hq (show col-1<p.directions+1 by dsimp [stride] at hc;omega)
          have addr : p.scratch+q*(p.directions+1)+(col-1)<p.resources := by
            omega
          rw [before _ addr])
  intro P R K machine
  exact PhysicalProcedure.Procedure.Spec.mono
    (A := (scratchPass W ctrl).seq (resourcePass W ctrl))
    (first.seq second (fun _ _ eqn=>eqn))
    (fun _ e=>e) (by rintro _ o ⟨x,_,z⟩;exact z) le_rfl machine

/-- Direct physical readback of the published row. The resource sizes are
exact even when a scratch cell was interpreted modulo the native word width. -/
theorem completed_cell {W ctrl header : ℕ} (p : Parameters ℕ) (r : Room W ctrl header p)
    (m old : Memory W) (dest : Fin p.lanes → Fin p.roots)
    (lists : TraceIntervalScanner.Output p.heads p.links dest old m) (v : Fin p.roots)
    (j : Fin (p.directions+2)) :
    completed p m (p.resources+v.val*(p.directions+2)+j.val) =
      if j.val=0 then m (p.charges+2*(p.firstFinal+v.val))
      else (rootSum dest v (fun q=>laneValue p q (j.val-1)) : Word W) := by
  let tmp := intermediate p m
  have hv := v.isLt
  have hj := j.isLt
  have row := Nat.mul_le_mul_right (p.directions+2) (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at row
  have cell : v.val*(p.directions+2)+j.val<resourceLength p := by dsimp [resourceLength];omega
  unfold completed
  rw [fillSegment]
  rw [ite_eq_left (show p.resources≤p.resources+v.val*(p.directions+2)+j.val ∧
    p.resources+v.val*(p.directions+2)+j.val<p.resources+resourceLength p by constructor <;> omega)]
  rw [resource_index _ _ _ _ hj]
  by_cases zero : j.val=0
  · simp only [ite_eq_left zero,Fin.cast_val_eq_self]
    exact immutable_small m _ _ (by have := r.costs;omega)
  · simp only [ite_eq_right zero,Fin.cast_val_eq_self]
    have head : tmp (p.heads+v.val)=m (p.heads+v.val) := immutable_small m _ _ (by have := r.heads;omega)
    rw [show intermediate p m (p.heads+v.val)=_ from head]
    let t:=ptrRow p.lanes (m (p.heads+v.val)).val
    let stride:=p.directions+1
    let col:=j.val-1
    have tc : t≤p.lanes := by dsimp [t,ptrRow];split <;> omega
    have hcol : col<stride := by dsimp [col,stride];omega
    have atCell : t*stride+col<scratchLength p := scratch_offset tc hcol
    change intermediate p m (p.scratch+t*stride+col)=_
    simp only [intermediate,fillSegment,show p.scratch≤p.scratch+t*stride+col by omega,
      show p.scratch+t*stride+col<p.scratch+scratchLength p by omega,and_self,ite_true,scratchWord,
      show p.scratch+t*stride+col-p.scratch=t*stride+col by omega]
    change (cumulative p.lanes _ (fun q=>laneValue p q ((t*stride+col)%stride)) ((t*stride+col)/stride) : Word W)=_
    rw [Nat.mul_add_mod_of_lt hcol, Nat.mul_comm t stride, Nat.mul_add_div (by dsimp [stride];omega : 0<stride),
      Nat.div_eq_of_lt hcol,Nat.add_zero]
    exact congrArg (fun z : ℕ=>(z:Word W)) (cumulative_root lists v (fun q=>laneValue p q col))

theorem published_input {W ctrl header : ℕ} (p : Parameters ℕ) (r : Room W ctrl header p)
    (m old : Memory W) (dest : Fin p.lanes→Fin p.roots)
    (lists : TraceIntervalScanner.Output p.heads p.links dest old m) (v : Fin p.roots) :
    completed p m (p.resources+v.val*(p.directions+2)+1)=(inputCount dest v p.cap p.pairSpan : Word W) := by
  have weights : (fun q=>laneValue p q 0)=FactorPinIntervals.bucketLength p.cap (2*p.pairSpan) :=
    funext (laneValue_bits p)
  simpa [inputCount,weights] using completed_cell p r m old dest lists v
    (⟨1,by omega⟩ : Fin (p.directions+2))

theorem published_direction {W ctrl header : ℕ} (p : Parameters ℕ) (r : Room W ctrl header p)
    (m old : Memory W) (dest : Fin p.lanes→Fin p.roots)
    (lists : TraceIntervalScanner.Output p.heads p.links dest old m) (v : Fin p.roots) (i : Fin p.directions) :
    completed p m (p.resources+v.val*(p.directions+2)+(2+i.val))=
      (directionCount dest v p.band p.pairSpan i.val : Word W) := by
  simpa [directionCount,laneValue_direction,show 2+i.val-1=i.val+1 by omega] using
    completed_cell p r m old dest lists v (⟨2+i.val,by have := i.isLt;omega⟩ : Fin (p.directions+2))

end Hierarchy.TraceAdmission.Resources

end OAI
