import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Transpose the old group radix into the successor block and expand the host -/
namespace Hierarchy.DescentScalarBookReshape
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H Q J r a M w : ℕ}

abbrev Seat (H Q J r M : ℕ) := Fin r×Row (H*Q) J M

def ordinal (H Q J r M : ℕ) : Seat H Q J r M≃Fin (r*((H*Q)*chunks J M)) :=
  ((Equiv.refl _).prodCongr (row (H*Q) J M)).trans finProdFinEquiv

def origin (z : Seat H Q J r M) : Row H J M:=((finProdFinEquiv.symm z.2.1).1,z.2.2)
def low (z : Seat H Q J r M) : Fin Q:=(finProdFinEquiv.symm z.2.1).2

def sourceOffset (z : Seat H Q J r M) :=(low z).val*(H*chunks J M)+(row H J M (origin z)).val

def book (select : Fin Q→Fin H→Fin (J*r)→Cell a) (b : Fin r) (h : Fin (H*Q)) (g : Fin J) :=
  let pair:=finProdFinEquiv.symm h
  select pair.2 pair.1 (finProdFinEquiv (g,b))

def project (i : Fin r) (x : Cell (a*r)) :=(encode a r).symm x i

private theorem zero (a r : ℕ) : encode a r (fun _=>0)=0 :=by apply Fin.ext;change (finFunctionFinEquiv (fun _ : Fin r=>(0:Cell a))).val=0;simp []

theorem page_read (x : Fin Q→Fin H→Fin (J*r)→Cell a) (z : Seat H Q J r M) :
    DescentSIMDLookup.table (M:=M) (project z.1) (data (groupedRows (x (low z))) (origin z))=
      data (book x z.1) z.2 :=by
  simp only [DescentSIMDLookup.table,data,Equiv.symm_apply_apply]
  apply congrArg (encode a M);funext t
  change project z.1 (if live:z.2.2.val*M+t.val<J then groupedRows (x (low z)) (origin z).1 ⟨_,live⟩ else 0)=_
  by_cases yes:z.2.2.val*M+t.val<J
  · simp [yes,project,groupedRows,low,origin,book]
  · have back: (encode a r).symm 0=(fun _=>0):=(encode a r).symm_apply_eq.mpr (zero a r).symm
    simp [yes,project,back]

abbrev Index (H Q J r a M : ℕ) := (Fin r×Cell ((a*r)*M)) ⊕ (Fin 2×Fin (r*((H*Q)*chunks J M)))
def cells (H Q J r a M : ℕ) :=r*2^((a*r)*M)+2*(r*((H*Q)*chunks J M))

def index (H Q J r a M : ℕ) : Index H Q J r a M≃Fin (cells H Q J r a M) :=
  (finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv

def value : Index H Q J r a M→ℕ
  | .inl (b,x)=>(DescentSIMDLookup.table (M:=M) (project (a:=a) b) x).val
  | .inr (f,i)=>let z:=(ordinal H Q J r M).symm i;if f.val=0 then sourceOffset z else z.1.val*2^((a*r)*M)

def words (H Q J r a M j : ℕ) :=if yes:j<cells H Q J r a M then value ((index H Q J r a M).symm ⟨j,yes⟩) else 0

def address (base : ℕ) : Index H Q J r a M→ℕ
  | .inl (b,x)=>base+(b.val*2^((a*r)*M)+x.val)
  | .inr (f,i)=>base+r*2^((a*r)*M)+f.val*(r*((H*Q)*chunks J M))+i.val

def mounted (base H Q J r a M : ℕ) (m : Memory w) :=DescentStaticWordColumn.image base (words H Q J r a M) m (cells H Q J r a M)

theorem statics (base : ℕ) (m : Memory w) (i : Index H Q J r a M) : mounted base H Q J r a M m (address base i)=(value i:Word w) :=by
  have location : address base i=base+(index H Q J r a M i).val := by
    rcases i with ⟨j,x⟩|⟨j,x⟩
    · change base+_ = base+(finSumFinEquiv (Sum.inl (finProdFinEquiv (j,x))) : Fin (cells H Q J r a M)).val
      rw [finSumFinEquiv_apply_left];
        change base+(j.val*2^((a*r)*M)+x.val)=base+(finProdFinEquiv (j,x)).val;
        rw [finProdFinEquiv_apply_val]; ring
    · change base+_+_+_ = base+(finSumFinEquiv (Sum.inr (finProdFinEquiv (j,x))) : Fin (cells H Q J r a M)).val
      rw [finSumFinEquiv_apply_right];
        change _=base+(r*2^((a*r)*M)+(finProdFinEquiv (j,x)).val);
        rw [finProdFinEquiv_apply_val]; ring
  rw [location,mounted,DescentStaticWordColumn.read _ _ _ _ (index H Q J r a M i).isLt]
  simp only [words,dite_eq_left (index H Q J r a M i).isLt]
  change (value ((index H Q J r a M).symm (index H Q J r a M i)):Word w)=_
  rw [Equiv.symm_apply_apply]

structure Chart where
  source : Bank
  dictionary : Bank
  srcRow : Bank
  offset : Bank

def layout (H Q J r a M base : ℕ) (old : Bank) : Chart :=
  let n:=r*((H*Q)*chunks J M);let bits:=Nat.clog 2 (n+1);let at_:=base+r*2^((a*r)*M)
  ⟨old,⟨base,Nat.clog 2 (r*2^((a*r)*M)+1)⟩,⟨at_,bits⟩,⟨at_+n,bits⟩⟩

def expression (C : Chart) : Expr:=.lookup C.dictionary (.op .add (.lookup C.offset .row) (.lookup C.source (.lookup C.srcRow .row)))

def program (H Q J r a M base out w : ℕ) (old : Bank) :=
  (DescentStaticWordColumn.program w base (words H Q J r a M) (cells H Q J r a M)).seq
    (scan w out (r*((H*Q)*chunks J M)) (expression (layout H Q J r a M base old)))

structure Room (H Q J r a M w base out : ℕ) (old : Bank) : Prop where
  banks : (expression (layout H Q J r a M base old)).Fits w out
  sourceEnd : old.base+Q*(H*chunks J M)≤base
  capacity : Q*(H*chunks J M)≤old.size
  early : base+cells H Q J r a M≤out
  end_ : out+r*((H*Q)*chunks J M)<2^w

def result (H Q J r a M base out : ℕ) (old : Bank) (m : Memory w) :=
  image out (r*((H*Q)*chunks J M)) (expression (layout H Q J r a M base old)) (mounted base H Q J r a M m)

def dest (H Q J M base : ℕ) (b : Fin r) :=base+b.val*((H*Q)*chunks J M)

theorem run (base out : ℕ) (old : Bank) (m : Memory w) (x : Fin Q→Fin H→Fin (J*r)→Cell a) (hm : 0<M) (hr : 0<r)
    (fit : Room H Q J r a M w base out old)
    (source : ∀l (p : Row H (J*r) (M*r)),m (old.base+l.val*(H*chunks J M)+(row H (J*r) (M*r) p).val)=((data (x l) p).val:Word w)) :
    let n:=r*((H*Q)*chunks J M);let done:=result H Q J r a M base out old m
    (program H Q J r a M base out w old).Exec m done ((4+10*cells H Q J r a M)+(4+n*54)) ∧
      (∀b (p : Row (H*Q) J M),done (dest H Q J M out b+(row (H*Q) J M p).val)=((data (book x b) p).val:Word w)) ∧
      (∀u,u<base ∨ out+n≤u→done u=m u) :=by
  intro n done
  let C:=layout H Q J r a M base old;let mid:=mounted base H Q J r a M m
  have ds:C.dictionary.Fits w out:=fit.banks.1
  have off:C.offset.Fits w out:=fit.banks.2.1.1
  have rd:C.srcRow.Fits w out:=fit.banks.2.2.2.1
  have orig:old.Fits w out:=fit.banks.2.2.1
  have rowCap:n≤C.offset.size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have dictCap:r*2^((a*r)*M)≤C.dictionary.size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have before (u : ℕ) (earlier:u<base):mid u=m u:=DescentStaticWordColumn.frame _ _ _ _ _ (.inl earlier)
  have head : (DescentStaticWordColumn.program w base (words H Q J r a M) (cells H Q J r a M)).Exec m mid (4+10*cells H Q J r a M):=DescentStaticWordColumn.mount base (cells H Q J r a M) (words H Q J r a M) m (fit.early.trans_lt ((Nat.le_add_right ..).trans_lt fit.end_))
  have ran : (scan w out n (expression C)).Exec mid done (4+n*54):=scan_exec out n (expression C) mid fit.banks fit.end_
  refine ⟨(by intro P R K machine;exact Procedure.Exec.then head ran machine),?_,?_⟩
  · intro b p
    let z:Seat H Q J r M:=(b,p);let j:=ordinal H Q J r M z;let t:=data (groupedRows (x (low z))) (origin z)
    have dest_ : dest H Q J M out b+(row (H*Q) J M p).val=out+j.val:=by simp [dest,j,z,ordinal,finProdFinEquiv_apply_val]; ring
    have range_ {c l : ℕ} (i : Fin c) (j : Fin l) : i.val*l+j.val<c*l:=(Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ i.isLt)
    have rowSmall:=j.isLt.trans_le rowCap
    have oldSmall:sourceOffset z<Q*(H*chunks J M):=range_ (low z) (row H J M (origin z))
    have key:b.val*2^((a*r)*M)+t.val<C.dictionary.size:=(range_ b t).trans_le dictCap
    have atOld:m (old.base+sourceOffset z)=(t.val:Word w):=by
      simpa only [sourceOffset,Nat.add_assoc,t] using regroup_read hm hr (old.base+(low z).val*(H*chunks J M)) m (x (low z)) (source (low z)) (origin z)
    have get:C.srcRow.read mid (j.val:Word w)=(sourceOffset z:Word w):=by
      rw [bank_read C.srcRow mid (show j.val<C.srcRow.size from rowSmall) rd]
      simpa [C,layout,address,value,j,z] using statics base m (.inr ((0:Fin 2),j) : Index H Q J r a M)
    have bias:C.offset.read mid (j.val:Word w)=((b.val*2^((a*r)*M):ℕ):Word w):=by
      rw [bank_read C.offset mid rowSmall off]
      simpa [C,layout,address,value,j,z] using statics base m (.inr ((1:Fin 2),j) : Index H Q J r a M)
    rw [dest_];apply (ProtocolRAMGeneratedWrite.read_image out n (expression C) mid j).trans
    change C.dictionary.read mid (C.offset.read mid (j.val:Word w)+old.read mid (C.srcRow.read mid (j.val:Word w)))=_
    rw [get,bias,bank_read _ _ (oldSmall.trans_le fit.capacity) orig,before _ ((Nat.add_lt_add_left oldSmall _).trans_le fit.sourceEnd),atOld,←Nat.cast_add,bank_read _ _ key ds]
    exact (statics base m (.inl (b,t) : Index H Q J r a M)).trans (congrArg (fun q : Cell (a*M)=>(q.val:Word w)) (page_read x z))
  · intro u safe;rcases safe with low|high
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ u (.inl (low.trans_le ((Nat.le_add_right ..).trans fit.early)))).trans (before _ low)
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ u (.inr high)).trans (DescentStaticWordColumn.frame _ _ _ _ _ (.inr (fit.early.trans ((Nat.le_add_right ..).trans high))))

/-- Fresh output also clears the unused tail of each fitted power-of-two
index bank. The dictionary and both row indices use the same literal
addresses as the dense initializer. -/
def output (base H Q J r a M : ℕ) :=
  let n:=r*((H*Q)*chunks J M);let words:=r*2^((a*r)*M)
  base+cells H Q J r a M+2^Nat.clog 2 (words+1)+2^Nat.clog 2 (n+1)

theorem allocation_bounds (base width n dw iw : ℕ) :
    let top := base+width+2*n+dw+iw
    base ≤ top ∧ base+dw ≤ top ∧ base+width+iw ≤ top ∧
      base+width+n+iw ≤ top ∧ base+(width+2*n) ≤ top := by
  dsimp only
  omega

theorem arranged (base : ℕ) (old : Bank) (early : old.Fits w base)
    (area : Q*(H*chunks J M)≤old.size) (space : output base H Q J r a M+r*((H*Q)*chunks J M)<2^w) :
    Room H Q J r a M w base (output base H Q J r a M) old :=by
  let n:=r*((H*Q)*chunks J M);let width:=r*2^((a*r)*M);let out:=output base H Q J r a M
  let dw:=(2:ℕ)^Nat.clog 2 (width+1);let iw:=(2:ℕ)^Nat.clog 2 (n+1)
  have length_:out=base+width+2*n+dw+iw:=by dsimp [out,output,cells,width,n,dw,iw];omega
  obtain ⟨baseOut,dictEnd,srcEnd,offEnd,cellsEnd⟩ := allocation_bounds base width n dw iw
  rw [← length_] at baseOut dictEnd srcEnd offEnd cellsEnd
  have inside:out<2^w:=(Nat.le_add_right ..).trans_lt space
  have earlier : old.Fits w out:=⟨early.1,early.2.1,early.2.2.trans baseOut⟩
  have bank (B : Bank) (valid : B.base+B.size≤out):B.Fits w out:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (valid.trans_lt inside),valid⟩
  let c:=layout H Q J r a M base old
  have dictionary:c.dictionary.Fits w out:=bank _ dictEnd
  have ix:c.srcRow.Fits w out:=bank _ srcEnd
  have bias:c.offset.Fits w out:=bank _ offEnd
  refine ⟨?_,(Nat.add_le_add_left area _).trans early.2.2,area,?_,space⟩
  · exact ⟨dictionary,⟨bias,trivial⟩,earlier,ix,trivial⟩
  · exact cellsEnd

/-- Unconditional execution of the page projection and geometry transpose. -/
theorem exec (base out : ℕ) (old : Bank) (m : Memory w) (s : Room H Q J r a M w base out old) :
    (program H Q J r a M base out w old).Exec m (result H Q J r a M base out old m)
      ((4+10*cells H Q J r a M)+(4+(r*((H*Q)*chunks J M))*54)) :=by
  have first : (DescentStaticWordColumn.program w base (words H Q J r a M) (cells H Q J r a M)).Exec m (mounted base H Q J r a M m) (4+10*cells H Q J r a M):=DescentStaticWordColumn.mount base (cells H Q J r a M) (words H Q J r a M) m (s.early.trans_lt ((Nat.le_add_right ..).trans_lt s.end_))
  intro P R K machine
  exact Procedure.Exec.then first (scan_exec out _ (expression (layout H Q J r a M base old)) _ s.banks s.end_) machine

end
end Hierarchy.DescentScalarBookReshape

end OAI
