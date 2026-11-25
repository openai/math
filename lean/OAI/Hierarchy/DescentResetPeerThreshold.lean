import OAI.Hierarchy.DescentRelativeThreshold
import OAI.Hierarchy.DescentResetSelfPortsRAM
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # Sixteen receiver-shared threshold words read from two physical host directories -/
noncomputable section
namespace Hierarchy.DescentResetPeerThreshold
open DescentSIMDLookup DescentPackedColony DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

def stride (H : ℕ) := 2^Nat.clog 2 H
def outBase (base H : ℕ) := base+3*stride H
def endAddress (base H : ℕ) := outBase base H+16*H+stride H
def table (base H s : ℕ) : Bank:=⟨base+s*stride H,Nat.clog 2 H⟩
def thresholdBank (base H : ℕ) (d j : Fin 4) : Bank := ⟨outBase base H+(d.val*4+j.val)*H,Nat.clog 2 H⟩
def shape (width s h : ℕ) := if s=0 then h/width else if s=1 then 2+h%width else 4*h
def literal (width H i : ℕ) :=shape width (i/stride H) (i%stride H)

def donor (base H oldH : ℕ) (old : Bank) (d : Fin 4) :=
  let root:=Expr.lookup (table base H 0) .row
  let two:=Expr.op .add root root
  Expr.branch .lt root (.lit oldH) (.lookup old (.op .add (.op .add two two) (.lit d.val))) (.lit oldH)
def peer (base H : ℕ) (now : Bank) (j : Fin 4) :=
  Expr.lookup now (.op .add (.lookup (table base H 2) .row) (.lit j.val))
def expr (base H oldH : ℕ) (old now : Bank) (d j : Fin 4) :=
  let other:=peer base H now j
  let root:=Expr.lookup (table base H 0) other
  let center:=donor base H oldH old d
  Expr.branch .lt other (.lit H)
    (.branch .lt center (.lit oldH)
      (.branch .lt root center (.lit 1) (.branch .eq root center (.lookup (table base H 1) other) (.lit 0))) (.lit 0)) (.lit 0)

def expressions (base H oldH : ℕ) (old now : Bank) := List.ofFn fun i : Fin (4*4)=>
  let p : Fin 4×Fin 4:=finProdFinEquiv.symm i
  expr base H oldH old now p.1 p.2
def passes (base H oldH : ℕ) (old now : Bank) := ProbeStage.Native.columns H (outBase base H) (expressions base H oldH old now)
def program (base H oldH width w : ℕ) (old now : Bank) :=
  (DescentStaticWordColumn.program w base (literal width H) (3*stride H)).seq (ProtocolRAM.program w (passes base H oldH old now))
def memory {w : ℕ} (base H oldH width : ℕ) (old now : Bank) (m : Memory w) :=
  result (passes base H oldH old now) (DescentStaticWordColumn.image base (literal width H) m (3*stride H))
def ticks (base H oldH : ℕ) (old now : Bank) := (4+10*(3*stride H))+clock (passes base H oldH old now)

theorem work (base H oldH : ℕ) (old now : Bank) (d j : Fin 4) : (expr base H oldH old now d j).work≤300 := by
  simp [expr,donor,peer,Expr.work]

theorem ticks_le (base H oldH : ℕ) (old now : Bank) :
    ticks base H oldH old now≤(4+10*(3*stride H))+(4+16*(4+H*604)) := by
  have each e (hit : e∈expressions base H oldH old now) : e.work≤300 := by
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hit
    exact work ..
  exact Nat.add_le_add_left (by simpa [passes,expressions] using
    ProbeStage.Native.columns_clock H (outBase base H) 300 (expressions base H oldH old now) each) _

private theorem emitted_names {w : ℕ} (H base : ℕ) (es : List Expr) (all : ∀e∈es,e.work≤300) :
    DescentStaticWordColumn.names (ProtocolRAM.program w (ProbeStage.Native.columns H base es))≤15+es.length*1211 := by
  induction es generalizing base with
  | nil=>rw [ProbeStage.Native.columns,ProtocolRAM.program,DescentStaticWordColumn.names_scan];decide
  | cons e es ih=>
    have first:=all e (.head _)
    have rest:=ih (base+H) (fun y hy=>all y (.tail _ hy))
    rw [ProbeStage.Native.columns,ProtocolRAM.program,DescentStaticWordColumn.names_seq]
    change DescentStaticWordColumn.names (scan w base H e)+_≤_
    rw [DescentStaticWordColumn.names_scan,List.length_cons,Nat.succ_mul]
    omega

theorem names_le (base H oldH width w : ℕ) (old now : Bank) :
    DescentStaticWordColumn.names (program base H oldH width w old now)≤15*(3*stride H+1)+(15+16*1211) := by
  have bound:=emitted_names (w:=w) H (outBase base H) (expressions base H oldH old now) (fun e hit=>by
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hit;exact work ..)
  rw [program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount]
  exact Nat.add_le_add_left (by simpa [passes,expressions] using bound) _

private theorem tableFits {w base H s : ℕ} (index : s<3) (room : outBase base H<2^w) :
    (table base H s).Fits w (outBase base H) := by
  let p:=stride H
  have stop := Nat.mul_le_mul_right p index
  rw [Nat.succ_mul] at stop
  change 0<p ∧ p<2^w ∧ base+s*p+p≤base+3*p
  change base+3*p<2^w at room
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

theorem exprFits {w base H oldH : ℕ} (old now : Bank) (d j : Fin 4)
    (oldFit : old.Fits w base) (newFit : now.Fits w base) (room : outBase base H<2^w) :
    (expr base H oldH old now d j).Fits w (outBase base H) := by
  have grow (v : Bank) (h : v.Fits w base) : v.Fits w (outBase base H):=⟨h.1,h.2.1,h.2.2.trans (Nat.le_add_right ..)⟩
  simp [expr,peer,donor,Expr.Fits,tableFits (s:=0) (by decide) room,tableFits (s:=1) (by decide) room,
    tableFits (s:=2) (by decide) room,grow old oldFit,grow now newFit]

theorem any {w H oldH : ℕ} (base width : ℕ) (old now : Bank) (m : Memory w)
    (oldFit : old.Fits w base) (newFit : now.Fits w base) (room : endAddress base H<2^w) :
    let o:=memory base H oldH width old now m
    (program base H oldH width w old now).Exec m o (ticks base H oldH old now) ∧
      (∀z,z<base ∨ endAddress base H≤z → o z=m z) ∧ CheapCode (program base H oldH width w old now) := by
  intro o
  let start:=outBase base H
  let hdr:=DescentStaticWordColumn.image base (literal width H) m (3*stride H)
  let es:=expressions base H oldH old now
  have len : es.length=16:=by simp [es,expressions]
  have end_ : start+es.length*H<2^w := by rw [len];exact (Nat.le_add_right ..).trans_lt room
  have top : start<2^w:=(Nat.le_add_right ..).trans_lt end_
  have src e (hit : e∈es):e.Fits w start:=by obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hit;exact exprFits old now _ _ oldFit newFit top
  refine ⟨?_,?_,?_⟩
  · intro P R K machine
    exact Procedure.Exec.then (@DescentStaticWordColumn.mount w base (3*stride H) (literal width H) m top)
      (@ProbeStage.Native.columns_exec w H start es hdr (ProbeStage.Native.columns_safe es le_rfl src end_)) machine
  · intro z away
    obtain l|r:=away
    · exact (ProbeStage.Native.columns_frame es hdr (.inl (l.trans_le (Nat.le_add_right ..)))).trans
        (DescentStaticWordColumn.frame base _ _ m _ (.inl l))
    · have stop : start+es.length*H≤endAddress base H := by rw [len];exact Nat.le_add_right ..
      exact (ProbeStage.Native.columns_frame es hdr (.inr (stop.trans r))).trans
        (DescentStaticWordColumn.frame base _ _ m _ (.inr ((Nat.le_add_right ..).trans (stop.trans r))))
  · exact cheap_seq (DescentStaticWordColumn.cheap w base (literal width H) (3*stride H))
      (program_cheap _ (passes base H oldH old now))

def donorAt {H oldH : ℕ} (width : ℕ) (old : Fin oldH→Fin 4→Option (Fin oldH)) (r : Fin H) (d : Fin 4) :=
  if real : r.val/width<oldH then old ⟨_,real⟩ d else none

def value {H oldH : ℕ} (width : ℕ) (old : Fin oldH→Fin 4→Option (Fin oldH))
    (now : Fin H→Fin 4→Option (Fin H)) (r : Fin H) (d j : Fin 4) : ℕ :=
  (donorAt width old r d).elim 0 (fun center=>DescentRelativeClassChip.threshold width center.val ((now r j).map Fin.val))

/-- The scalar word sampled by the packed rank gate has its ordinary integer value. -/
theorem selected_value {H oldH w width : ℕ} (previous : Fin oldH→Fin 4→Option (Fin oldH))
    (current : Fin H→Fin 4→Option (Fin H)) (v : Fin H) (d j : Fin 4) (center : Fin oldH)
    (selected : donorAt width previous v d=some center) (positive : 0<width) (fits : width+2≤2^w) :
    ((value width previous current v d j:Word w)).val=
      DescentRelativeClassChip.threshold width center.val ((current v j).map Fin.val) := by
  simp only [value,selected,Option.elim_some]
  exact Fin.val_cast_of_lt ((DescentRelativeClassChip.threshold_room width center.val positive _).trans_le fits)

private theorem field_read {w H : ℕ} (base width : ℕ) (m : Memory w) (s : Fin 3) (r : Fin H) :
    DescentStaticWordColumn.image base (literal width H) m (3*stride H) (base+s.val*stride H+r.val)=
      (shape width s.val r.val:Word w) := by
  let p:=stride H
  have small : r.val<p:=r.isLt.trans_le (Nat.le_pow_clog (by decide) _)
  have hi : s.val*p+r.val<3*p:=(Nat.add_lt_add_left small _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ s.isLt)
  rw [Nat.add_assoc,DescentStaticWordColumn.read _ _ _ _ hi]
  have d : (s.val*p+r.val)/p=s.val:=by rw [Nat.mul_comm s.val p,Nat.mul_add_div (show 0<p from Nat.two_pow_pos _),Nat.div_eq_of_lt small,Nat.add_zero]
  have low : (s.val*p+r.val)%p=r.val:=by rw [Nat.mul_comm s.val p,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt small]
  exact congrArg (fun i : ℕ=>(i:Word w)) (congrArg₂ (shape width) d low)

private theorem comparison_lt {w x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    DescriptorExpr.Comparison.lt.test (x:Word w) (y:Word w)=decide (x<y) := by
  simp [DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

private theorem comparison_eq {w x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    DescriptorExpr.Comparison.eq.test (x:Word w) (y:Word w)=decide (x=y) := by
  by_cases yes : x=y
  · simp [DescriptorExpr.Comparison.test,yes]
  · have ne : (x:Word w)≠(y:Word w):=fun he=>yes (by
      simpa [Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy] using congrArg Fin.val he)
    simp [DescriptorExpr.Comparison.test,yes,ne]

/-- Four original donor classes and four unique new peer classes produce
sixteen thresholds, each shared across all groups in the receiving host. -/
theorem read {w H oldH : ℕ} (base width : ℕ) (old now : Bank) (m : Memory w)
    (previous : Fin oldH→Fin 4→Option (Fin oldH)) (current : Fin H→Fin 4→Option (Fin H))
    (oldFit : old.Fits w base) (newFit : now.Fits w base)
    (oldRows : oldH*4≤old.size) (newRows : H*4≤now.size)
    (prevRead : ∀(v : Fin oldH) (d : Fin 4),m (old.base+(v.val*4+d.val))=(target (previous v d):Word w))
    (nowRead : ∀(v : Fin H) (j : Fin 4),m (now.base+(v.val*4+j.val))=(target (current v j):Word w))
    (maxOld : oldH<2^w) (maxNew : H<2^w) (room : endAddress base H<2^w)
    (v : Fin H) (d j : Fin 4) :
    memory base H oldH width old now m ((thresholdBank base H d j).base+v.val)=
      (value width previous current v d j:Word w) := by
  let hdr:=DescentStaticWordColumn.image base (literal width H) m (3*stride H)
  let floor:=outBase base H
  have enough : floor<2^w:=((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans_lt room
  have range {n : ℕ} (r : Fin n) (i : Fin 4) : r.val*4+i.val<n*4 :=
    (Nat.add_lt_add_left i.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ r.isLt)
  have static (s : Fin 3) (r : Fin H) : (table base H s.val).read hdr (r.val:Word w)=
      (shape width s.val r.val:Word w) :=
    (bank_read _ _ (r.isLt.trans_le (Nat.le_pow_clog (by decide) _)) (tableFits s.isLt enough)).trans
      (field_read base width m s r)
  have rootRead (r : Fin H) : (table base H 0).read hdr (r.val:Word w)=(r.val/width : ℕ) := static 0 r
  have offsetRead (r : Fin H) : (table base H 1).read hdr (r.val:Word w)=(2+r.val%width : ℕ) := static 1 r
  have fourRead (r : Fin H) : (table base H 2).read hdr (r.val:Word w)=(4*r.val : ℕ) := static 2 r
  have prev (r : Fin oldH) (d : Fin 4) : old.read hdr ((r.val*4+d.val:ℕ):Word w)=(target (previous r d):Word w) :=
    (bank_read old _ ((range r d).trans_le oldRows) oldFit).trans
      ((DescentStaticWordColumn.frame base _ _ m _ (.inl ((Nat.add_lt_add_left ((range r d).trans_le oldRows) _).trans_le oldFit.2.2))).trans (prevRead r d))
  have present (r : Fin H) (j : Fin 4) : now.read hdr ((r.val*4+j.val:ℕ):Word w)=(target (current r j):Word w) :=
    (bank_read now _ ((range r j).trans_le newRows) newFit).trans
      ((DescentStaticWordColumn.frame base _ _ m _ (.inl ((Nat.add_lt_add_left ((range r j).trans_le newRows) _).trans_le newFit.2.2))).trans (nowRead r j))
  have donorBound : v.val/width<2^w := (Nat.div_le_self ..).trans_lt (v.isLt.trans maxNew)
  have atPeer : (peer base H now j).eval hdr (v.val:Word w)=(target (current v j):Word w) := by
    change now.read hdr ((table base H 2).read hdr (v.val:Word w)+(j.val:Word w))=_
    rw [fourRead]
    simpa only [Nat.cast_add,Nat.mul_comm 4] using present v j
  have atDonor : (donor base H oldH old d).eval hdr (v.val:Word w)=(target (donorAt width previous v d):Word w) := by
    simp only [donor,Expr.eval,rootRead v,RowOp.opcode,BinaryOp.eval,comparison_lt donorBound maxOld]
    by_cases occupied : v.val/width<oldH
    · simp only [occupied,decide_true,ite_true,donorAt,dite_eq_left]
      convert prev ⟨v.val/width,occupied⟩ d using 2
      push_cast
      ring
    · simp [occupied,donorAt,target]
  have term : (expr base H oldH old now d j).eval hdr (v.val:Word w)=(value width previous current v d j:Word w) := by
    cases nc : current v j with
    | none=>
      cases oc : donorAt width previous v d <;> simp [expr,Expr.eval,atPeer,nc,oc,target,comparison_lt maxNew maxNew,value,DescentRelativeClassChip.threshold]
    | some h=>
      have nh : h.val<2^w:=h.isLt.trans maxNew
      have rp : h.val/width<2^w:=(Nat.div_le_self ..).trans_lt nh
      cases oc : donorAt width previous v d with
      | none=>simp [expr,Expr.eval,atPeer,atDonor,nc,oc,target,comparison_lt nh maxNew,comparison_lt maxOld maxOld,h.isLt,value]
      | some o=>
        have oh:=o.isLt.trans maxOld
        by_cases lt : h.val/width<o.val <;> by_cases eq : h.val/width=o.val <;>
          simp [expr,Expr.eval,atPeer,atDonor,nc,oc,target,rootRead h,offsetRead h,
            comparison_lt nh maxNew,comparison_lt oh maxOld,comparison_lt rp oh,comparison_eq rp oh,
            comparison_lt oh oh,comparison_eq oh oh,
            h.isLt,o.isLt,value,DescentRelativeClassChip.threshold,lt,eq]
  let es:=expressions base H oldH old now
  let index:Fin (4*4):=finProdFinEquiv (d,j)
  have same : index.val=d.val*4+j.val:=by
    change j.val+4*d.val=d.val*4+j.val
    omega
  have len : es.length=4*4:=by simp [es,expressions]
  have ok e (hit : e∈es): e.Fits w floor:=by obtain ⟨ij,rfl⟩:=List.mem_ofFn.mp hit;exact exprFits old now _ _ oldFit newFit enough
  have sample:=ProbeStage.Native.columns_read es hdr le_rfl ok index.val (index.isLt.trans_eq len.symm) v
  change result (ProbeStage.Native.columns H floor es) hdr (floor+(d.val*4+j.val)*H+v.val)=_
  rw [←same,sample]
  simp only [es,expressions,List.getElem_ofFn,Fin.eta]
  rw [show finProdFinEquiv.symm index=(d,j) from finProdFinEquiv.symm_apply_apply (d,j)]
  exact term

theorem bank_fits {w : ℕ} (base H : ℕ) (d j : Fin 4) (room : endAddress base H<2^w) :
    (thresholdBank base H d j).Fits w (endAddress base H) ∧ H≤(thresholdBank base H d j).size := by
  have i : d.val*4+j.val<16 := by have x:=d.isLt;have y:=j.isLt;omega
  have mul:=Nat.mul_le_mul_right H i.le
  have p:=Nat.le_pow_clog (by decide : 1<2) H
  change (0<stride H ∧ stride H<2^w ∧ outBase base H+(d.val*4+j.val)*H+stride H≤endAddress base H) ∧ _
  change outBase base H+16*H+stride H<2^w at room
  unfold endAddress
  exact ⟨⟨Nat.two_pow_pos _,by omega,by omega⟩,p⟩

theorem extent (base H : ℕ) : endAddress base H=base+endAddress 0 H :=by simp [endAddress,outBase,Nat.add_assoc]
theorem bounded {ι : ℕ→Type*} {h : ∀t,ι t→ℕ} (paid : DescentDatedAddressBook.Bounded h) :
    DescentDatedAddressBook.Bounded (fun t i=>endAddress 0 (h t i)) :=
  ((((DescentDatedAddressBook.Bounded.const 0).add ((DescentDatedAddressBook.Bounded.const 3).mul paid.padded)).add
    ((DescentDatedAddressBook.Bounded.const 16).mul paid)).add paid.padded)

end Hierarchy.DescentResetPeerThreshold
end

end OAI
