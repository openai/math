import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Packed lookup in a measured, host-dependent short neighbor directory -/
namespace Hierarchy.DescentPackedChildNeighbor.SIMD
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G T a b M w out : ℕ}

/-- Zero marks an absent query. The same query dictionary is installed once for all hosts. -/
def field (j : Fin T) (x : Cell a) (value : Cell b) : Cell b := if x.val=j.val+1 then value else 0

def merge (left right : Cell b) : Cell b := if left=0 then right else left

def lookup (value : Fin T→Cell b) (x : Cell a) : List (Fin T)→Cell b
  | []=>0
  | j::js=>merge (field j x (value j)) (lookup value x js)

theorem lookup_at (value : Fin T→Cell b) (x : Cell a) (i : Fin T) (yes : x.val=i.val+1) (js : List (Fin T)) :
    lookup value x js=if i∈js then value i else 0 :=by
  induction js with
  | nil=>simp [lookup]
  | cons j js ih=>
    by_cases eqn:i=j
    · subst j;by_cases zero:value i=0 <;> by_cases mem:i∈js <;> simp [lookup,field,yes,merge,ih,zero,mem]
    · have different : i.val ≠ j.val := fun h => eqn (Fin.ext h)
      simp [lookup,field,yes,merge,different,ih,eqn]

theorem lookup_missing (value : Fin T→Cell b) (x : Cell a) (missing : ∀i : Fin T,x.val≠i.val+1) (js : List (Fin T)) : lookup value x js=0 :=by
  induction js with | nil=>rfl | cons j js ih=>simp [lookup,field,missing,merge,ih]

def pair (a b M : ℕ) : Cell (a*M)×Cell b ≃ Cell (a*M+b) :=finProdFinEquiv.trans (finCongr (pow_add 2 (a*M) b).symm)

def page (j : Fin T) (n : Cell (a*M+b)) : Cell (b*M) :=
  let z:=(pair a b M).symm n
  encode b M (fun i=>field j ((encode a M).symm z.1 i) z.2)

theorem page_at (j : Fin T) (x : Fin H→Fin G→Cell a) (value : Fin H→Cell b) (p : Row H G M) :
    page j (pair a b M (data x p,value p.1))=data (fun h g=>field j (x h g) (value h)) p :=by
  simp only [page,Equiv.symm_apply_apply,data]
  apply congrArg (encode b M);funext i
  by_cases live:p.2.val*M+i.val<G <;> simp [live,field]

structure Chart (T : ℕ) where
  header : Bank
  offset : Bank
  shift : Bank
  pages : Fin T→Bank
  join : Tables

def cell (C : Chart T) (query : Expr) (j : Fin T) : Expr :=
  .lookup (C.pages j) (.op .add (.lookup C.header (.op .add (.lookup C.offset .row) (.lit j.val))) (.lookup C.shift query))

def body (C : Chart T) (query : Expr) : List (Fin T)→Expr
  | []=>.lit 0
  | i::js=>C.join.read (cell C query i) (body C query js)

def code (C : Chart T) (query : Expr) (out H G M w : ℕ) :=scan w out (H*chunks G M) (body C query (List.finRange T))

structure Room (C : Chart T) (q : Expr) (H G a b M w out : ℕ) : Prop where
  qFits : q.Fits w out
  tableFits : C.header.Fits w out
  offFits : C.offset.Fits w out
  shiftFits : C.shift.Fits w out
  pageFits : ∀j,(C.pages j).Fits w out
  joinShift : C.join.shift.Fits w out
  joinApply : C.join.apply.Fits w out
  headers : H*T≤C.header.size
  rows : H*chunks G M≤C.offset.size
  shifts : C.shift.bits=a*M
  pages : ∀j,(C.pages j).bits=a*M+b
  joinLeft : C.join.shift.bits=b*M
  joinBoth : C.join.apply.bits=(b+b)*M
  endFits : out+H*chunks G M<2^w

structure Stored (C : Chart T) (H G a b M : ℕ) (value : Fin H→Fin T→Cell b) (m : Memory w) : Prop where
  values : ∀v j,m (C.header.base+(v.val*T+j.val))=((value v j).val:Word w)
  offsets : ∀p : Row H G M,m (C.offset.base+(row H G M p).val)=((p.1.val*T:ℕ):Word w)
  shifts : ∀n : Cell (a*M),m (C.shift.base+n.val)=((2^b*n.val:ℕ):Word w)
  pages : ∀j (n : Cell (a*M+b)),m ((C.pages j).base+n.val)=((page (a:=a) (b:=b) (M:=M) j n).val:Word w)
  joins : Static C.join (merge (b:=b)) M m

private theorem cell_fit (C : Chart T) (q : Expr) (ok : Room C q H G a b M w out) (j : Fin T) : (cell C q j).Fits w out :=
  ⟨ok.pageFits j,⟨ok.tableFits,⟨⟨ok.offFits,trivial⟩,trivial⟩⟩,⟨ok.shiftFits,ok.qFits⟩⟩

theorem fitted (C : Chart T) (q : Expr) (ok : Room C q H G a b M w out) (js : List (Fin T)) : (body C q js).Fits w out :=by
  induction js with
  | nil=>trivial
  | cons j js ih=>exact ⟨ok.joinApply,ih,ok.joinShift,cell_fit C q ok j⟩

private theorem fetched (C : Chart T) (q : Expr) (out : ℕ) (ok : Room C q H G a b M w out) (value : Fin H→Fin T→Cell b) (m : Memory w)
    (stored : Stored C H G a b M value m) (x : Fin H→Fin G→Cell a) (source : Source q x M m) (j : Fin T) :
    Source (cell C q j) (fun v g=>field j (x v g) (value v j)) M m :=by
  intro p
  have off:=(row H G M p).isLt.trans_le ok.rows
  have col:p.1.val*T+j.val<C.header.size:= (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact (Nat.mul_le_mul_right T p.1.isLt).trans ok.headers)
  have sh:(data x p).val<C.shift.size:=by simpa only [Bank.size,ok.shifts] using (data x p).isLt
  let ix:=pair a b M (data x p,value p.1 j)
  have lo:ix.val<(C.pages j).size:=by simpa only [Bank.size,ok.pages] using ix.isLt
  change (C.pages j).read m (C.header.read m (C.offset.read m ((row H G M p).val:Word w)+(j.val:Word w))+C.shift.read m (q.eval m _))=_
  rw [bank_read C.offset m off ok.offFits,stored.offsets,←Nat.cast_add,bank_read C.header m col ok.tableFits,stored.values,source p,bank_read C.shift m sh ok.shiftFits,stored.shifts,←Nat.cast_add]
  change (C.pages j).read m (ix.val:Word w)=_
  rw [bank_read _ m lo (ok.pageFits j),stored.pages]
  exact congrArg (fun z : Cell (b*M)=>(z.val:Word w)) (page_at j x (fun h=>value h j) p)

theorem measures (C : Chart T) (q : Expr) (out : ℕ) (ok : Room C q H G a b M w out) (value : Fin H→Fin T→Cell b) (m : Memory w)
    (stored : Stored C H G a b M value m) (x : Fin H→Fin G→Cell a) (source : Source q x M m) (js : List (Fin T)) :
    Source (body C q js) (fun v g=>lookup (value v) (x v g) js) M m :=by
  induction js with
  | nil=>
    intro p
    change (0:Word w)=((finFunctionFinEquiv (fun i : Fin M=>if _ : p.2.val*M+i.val<G then (0:Cell b) else 0)).val:Word w)
    simp
  | cons j js ih=>
    exact read_data C.join _ _ out ⟨cell_fit C q ok j,fitted C q ok js,ok.joinShift,ok.joinApply,ok.joinLeft,ok.joinBoth⟩ merge (by simp [merge]) m stored.joins _ _ (fetched C q out ok value m stored x source j) ih

theorem run (C : Chart T) (q : Expr) (out : ℕ) (ok : Room C q H G a b M w out) (value : Fin H→Fin T→Cell b) (m : Memory w)
    (stored : Stored C H G a b M value m) (x : Fin H→Fin G→Cell a) (source : Source q x M m) :
    let n:=H*chunks G M;let e:=body C q (List.finRange T);let done:=image out n e m
    (code C q out H G M w).Exec m done (4+n*(2*e.work+4)) ∧
      (∀p : Row H G M,done (out+(row H G M p).val)=((data (fun h g=>lookup (value h) (x h g) (List.finRange T)) p).val:Word w)) ∧
      (∀u,u<out ∨ out+n≤u→done u=m u) ∧ CheapCode (code C q out H G M w) :=by
  exact ⟨scan_exec _ _ _ _ (fitted C q ok _) ok.endFits,
    fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H G M p)).trans (measures C q out ok value m stored x source _ p),
    fun u h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ u h,@scan_cheap _ _ _ _⟩

theorem work (C : Chart T) (q : Expr) (js : List (Fin T)) : (body C q js).work=1+js.length*(q.work+36) :=by
  induction js with
  | nil=>simp [body,Expr.work]
  | cons j js ih=>simp only [body,DescentPackedZip.work,cell,Expr.work,ih,List.length_cons,Nat.succ_mul];omega

theorem digit_of_words (val : Fin H→Fin T→Cell b) (x : Fin H→Fin G→Cell a) (out : ℕ) (done : Memory w)
    (read : ∀p : Row H G M,done (out+(row H G M p).val)=((data (fun h g=>lookup (val h) (x h g) (List.finRange T)) p).val:Word w))
    (v : Fin H) (g : Fin G) (j : Fin T) (match_ : (x v g).val=j.val+1) (lanes : 0<M) (width : b*M≤w) :
    digit b (lane g lanes).val (done (out+(row H G M (position v g lanes)).val)).val=(val v j).val :=by
  let p:=position v g lanes
  let f:=fun v g=>lookup (val v) (x v g) (List.finRange T)
  have lo:(data f p).val<2^w:=(data f p).isLt.trans_le (Nat.pow_le_pow_right (by decide) width)
  have coord:p.2.val*M+(lane g lanes).val=g.val:=Nat.div_add_mod' ..
  have yes:p.2.val*M+(lane g lanes).val<G:=coord.trans_lt g.isLt
  have same:(⟨_,yes⟩ : Fin G)=g:=Fin.ext coord
  rw [read p,Fin.val_cast_of_lt lo]
  simp only [data,digit_encode,dite_eq_left yes,same]
  change (lookup (val v) (x v g) (List.finRange T)).val=(val v j).val
  rw [lookup_at _ _ _ match_,ite_eq_left (List.mem_finRange j)]

theorem digit_at (C : Chart T) (q : Expr) (out : ℕ) (ok : Room C q H G a b M w out) (val : Fin H→Fin T→Cell b) (m : Memory w)
    (stored : Stored C H G a b M val m) (x : Fin H→Fin G→Cell a) (source : Source q x M m) (v : Fin H) (g : Fin G)
    (j : Fin T) (match_ : (x v g).val=j.val+1) (lanes : 0<M) (width : b*M≤w) :
    let done:=image out (H*chunks G M) (body C q (List.finRange T)) m
    digit b (lane g lanes).val (done (out+(row H G M (position v g lanes)).val)).val=(val v j).val :=by
  exact digit_of_words val x out _ (run C q out ok val m stored x source).2.1 v g j match_ lanes width

end
end Hierarchy.DescentPackedChildNeighbor.SIMD

end OAI
