import OAI.Hierarchy.DescentResetOriginalPosted
import OAI.Hierarchy.DescentResetDonorBook
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # The public original-word phase, with contact labels folded from the old signed bank -/
namespace Hierarchy.DescentResetPublicOriginalPhase
open DescentSixParty.Chronology DescentResetMixedWordRAM DescentResetMixedWordRAM.OriginalDate
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {X Q K N H G w : ℕ}
structure Prior (X Q N : ℕ) where
  «meta» : Fin X→Fin (Q+1)→Expr
  zero : Fin X→Expr
  self : Fin X→Expr
  shape : Fin X→Expr
  label : Fin X→Bool→Fin N→Expr
  cargo : Fin X→Bool→Fin 2→Fin N→Expr

structure Layout (X Q K N : ℕ) where
  req : Fin Q→Bool×ℕ
  shelf : Fin (Q+1)↪Fin K
  fn : Fin 2→OriginalBooks.WordFn
  M : ℕ
  hosts : ℕ
  groups : ℕ
  selectorBits : ℕ
  shortBits : ℕ
  metaBits : ℕ
  zeroBits : ℕ
  resultBits : ℕ
  donor : ℕ
  format : ℕ
  original : ℕ
  old : Prior X Q N

namespace Layout
variable (L : Layout X Q K N)
def pages:=DescentResetDonorBook.page (fun j=>(L.req j).2) L.selectorBits L.shortBits L.M
def bits:=DescentResetDonorBook.width L.selectorBits L.shortBits L.M
def count:=DescentResetDonorBook.words Q L.selectorBits L.shortBits L.M
def donorExpr (x : Fin X) (j : Fin Q) (t : Fin 2):=
  DescentResetDonorBook.expression (fun c=>(L.req c).2) L.selectorBits L.shortBits L.M L.donor j
    (L.old.label x (L.req j).1) (L.old.cargo x (L.req j).1 t)
def fields : Fields X (Q+1) where
  «meta» p:=let (x,j):=finProdFinEquiv.symm p;L.old.meta x j
  zero p:=L.old.zero (finProdFinEquiv.symm p).1
  halo p:=let (x,j):=finProdFinEquiv.symm p;Fin.cases (L.old.self x) (fun s=>L.donorExpr x s 1) j
  arg p:=let (x,j):=finProdFinEquiv.symm p;Fin.cases (L.old.shape x) (fun s=>L.donorExpr x s 0) j
def date : Date X (Q+1) K:=⟨L.shelf,Fin.cases 0 (fun _=>1),L.format,L.original,L.hosts*chunks L.groups L.M,
  L.M,L.metaBits,L.zeroBits,L.shortBits,L.shortBits,L.resultBits,L.fn,L.fields⟩
def first (m : Memory w):=after L.pages L.bits L.donor m
def dst (m : Memory w):=L.date.dst (L.first m)
def cpu (w : ℕ):=(mount L.pages L.bits w L.donor).seq (L.date.code w)
def clock:=4+10*L.count+L.date.ticks

structure Room (w : ℕ) : Prop where
  «meta» : ∀ x j,(L.old.meta x j).Fits w L.donor
  zero : ∀ x,(L.old.zero x).Fits w L.donor
  self : ∀ x,(L.old.self x).Fits w L.donor
  shape : ∀ x,(L.old.shape x).Fits w L.donor
  label : ∀x s i,(L.old.label x s i).Fits w L.donor
  cargo : ∀x s t i,(L.old.cargo x s t i).Fits w L.donor
  donorEnd : L.donor+L.count≤L.format
  formatEnd : L.date.firstEnd≤L.original
  stop : L.date.stop<2^w

theorem dateRoom (r : L.Room w) : L.date.Room w:=by
  have head : L.format<2^w:=(Nat.le_add_right ..).trans_lt (r.formatEnd.trans_lt ((Nat.le_add_right ..).trans_lt r.stop))
  have early : L.donor≤L.format:=(Nat.le_add_right ..).trans r.donorEnd
  have op (x : Fin X) (j : Fin Q) (t : Fin 2) : (L.donorExpr x j t).Fits w L.format:=
    DescentResetDonorBook.fit _ _ _ _ _ _ _ _ _ (fun i=>⟨r.label ..,r.cargo ..⟩) r.donorEnd head
  refine ⟨r.formatEnd,r.stop,fun p=>ProtocolRAMGeneratedWrite.fits_mono _ early (r.meta ..),
    fun p=>ProtocolRAMGeneratedWrite.fits_mono _ early (r.zero ..),?_,?_⟩
  · intro p;obtain ⟨⟨x,j⟩,rfl⟩:=finProdFinEquiv.surjective p
    simp only [date,fields,Equiv.symm_apply_apply]
    exact Fin.cases (ProtocolRAMGeneratedWrite.fits_mono _ early (r.self x)) (fun j=>op x j 1) j
  · intro p;obtain ⟨⟨x,j⟩,rfl⟩:=finProdFinEquiv.surjective p
    simp only [date,fields,Equiv.symm_apply_apply]
    exact Fin.cases (ProtocolRAMGeneratedWrite.fits_mono _ early (r.shape x)) (fun j=>op x j 0) j

theorem any (r : L.Room w) (m : Memory w) : (L.cpu w).Exec m (L.dst m) L.clock ∧ CheapCode (L.cpu w) ∧
    ∀a,a<L.donor ∨ L.date.stop≤a→L.dst m a=m a:=by
  have rr:=L.dateRoom r
  have start:=(L.date.earlier rr).trans_lt (L.date.space rr)
  obtain ⟨first_,_,_,ret,cheap₀,_⟩:=DescentResetDonorBook.installed (fun j=>(L.req j).2) L.selectorBits L.shortBits L.M L.donor m (r.donorEnd.trans_lt start)
  obtain ⟨second,cheap₁,preserve⟩:=L.date.any rr (L.first m)
  refine ⟨first_.then second,cheap_seq cheap₀ cheap₁,?_⟩
  intro a side
  have eqn : L.dst m a=L.first m a:=by
    apply preserve
    · rcases side with lo|hi
      · exact .inl (lo.trans_le ((Nat.le_add_right ..).trans r.donorEnd))
      · exact .inr (r.formatEnd.trans ((Nat.le_add_right ..).trans hi))
    · intro i
      have cut:=DescentResetOriginalSlots.earlier L.shelf L.original L.date.rows L.date.expr
        ⟨_,_,_⟩ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
      rcases side with lo|hi
      · exact .inl (lo.trans_le (((Nat.le_add_right ..).trans r.donorEnd).trans ((L.date.earlier rr).trans cut.1)))
      · exact .inr (cut.2.trans hi)
  exact eqn.trans (ret a (side.imp id (fun hi=>r.donorEnd.trans ((L.date.earlier rr).trans ((Nat.le_add_right ..).trans hi)))))

def phase (r : L.Room w) : NativePhase w:=⟨L.cpu w,L.clock,L.dst,(L.any r (fun _=>0)).2.1⟩
theorem runs (r : L.Room w) (m : Memory w) : (L.phase r).Runs m:=(L.any r m).1

theorem retain_slot (r : L.Room w) (m : Memory w) (x : Fin X) (j : Fin K) (missing : ∀k,L.shelf k≠j) (i : Fin L.date.rows) :
    let addr:=DescentResetOriginalSlots.offset L.original L.date.rows K x.val j.val+i.val
    L.dst m addr=m addr:=by
  intro addr
  have init : L.donor+L.count≤addr:=by
    apply r.donorEnd.trans
    apply (L.date.earlier (L.dateRoom r)).trans
    change L.original≤L.original+(x.val*K+j.val)*DescentResetOriginalSlots.stride L.date.rows+i.val
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  exact (L.date.frame_slot (L.dateRoom r) (L.first m) x j missing i).trans (frame L.pages L.bits L.donor m addr (.inr init))

theorem price (r : L.Room w) (limit : ℕ) («meta» : ∀x j,(L.old.meta x j).work≤limit)
    (zero : ∀x,(L.old.zero x).work≤limit) (self : ∀x,(L.old.self x).work≤limit)
    (shape : ∀x,(L.old.shape x).work≤limit)
    (labels : ∀x s i,(L.old.label x s i).work≤limit) (payload : ∀x s t i,(L.old.cargo x s t i).work≤limit) :
    let cost:=2*limit+2*max limit (1+N*(2*limit+22))+33
    L.clock≤(4+10*L.count)+(4+10*(12*2^L.date.width)+(4+X*(Q+1)*(4+L.date.rows*(2*cost+4)))) ∧
    DescentStaticWordColumn.names (L.cpu w)≤15*(L.count+1)+(15*(12*2^L.date.width+1)+(15+X*(Q+1)*(11+4*cost))):=by
  intro cost
  have expr (x : Fin X) (j : Fin Q) (t : Fin 2) : (L.donorExpr x j t).work≤1+N*(2*limit+22):=by
    apply DescentResetDonorBook.price
    intro i;have a:=labels x (L.req j).1 i;have b:=payload x (L.req j).1 t i;omega
  have fam (p : Fin (X*(Q+1))) : (L.fields.meta p).work+(L.fields.zero p).work+(L.fields.halo p).work+(L.fields.arg p).work+33≤cost:=by
    obtain ⟨⟨x,j⟩,rfl⟩:=finProdFinEquiv.surjective p
    have m:=«meta» x j; have z:=zero x
    simp only [fields,Equiv.symm_apply_apply]
    induction j using Fin.cases with
    | zero=>simp only [Fin.cases_zero];have u:=(self x).trans (Nat.le_max_left limit (1+N*(2*limit+22)));have v:=shape x;dsimp [cost];omega
    | succ j=>simp only [Fin.cases_succ];have u:=expr x j 1;have v:=expr x j 0;dsimp [cost];omega
  have bill:=L.date.invoice (L.dateRoom r) cost fam
  exact ⟨Nat.add_le_add_left bill.1 _,by
    simpa only [cpu,DescentStaticWordColumn.names_seq,mount,DescentStaticWordColumn.names_mount,count,pages,bits,DescentResetDonorBook.words] using Nat.add_le_add_left bill.2 (15*(L.count+1))⟩

end Layout
end
end Hierarchy.DescentResetPublicOriginalPhase

end OAI
