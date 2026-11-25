import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # Reading packed sparse reset operands in true compact actor order -/
namespace Hierarchy.DescentResetDenseOperand
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {w H R G M b used : ℕ}

structure Layout where
  first : ℕ
  hosts : ℕ
  sparse : ℕ
  parts : ℕ

namespace Layout
variable (L : Layout)
def pitch := 2^Nat.clog 2 (L.hosts*L.parts)
def rawPitch := 2^Nat.clog 2 L.sparse
def host : Bank:=⟨L.first,Nat.clog 2 (L.hosts*L.parts)⟩
def low : Bank:=⟨L.first+L.pitch,Nat.clog 2 (L.hosts*L.parts)⟩
def stride : Bank:=⟨L.first+2*L.pitch,Nat.clog 2 L.sparse⟩
def size := 2*L.pitch+L.rawPitch
def endAddress:=L.first+L.size
def literal (j : ℕ) : ℕ :=
  if j<L.pitch then j/L.parts else if j<2*L.pitch then (j-L.pitch)%L.parts else (j-2*L.pitch)*L.parts
def setup (w : ℕ) := DescentStaticWordColumn.program w L.first L.literal L.size
def mounted (m : Memory w) := DescentStaticWordColumn.image L.first L.literal m L.size
def index (inv : Bank) : Expr := .op .add (.lookup L.low .row)
  (.lookup L.stride (.lookup inv (.lookup L.host .row)))
def load (cnt inv : Bank) (e : Expr) : Expr :=
  .branch .lt (.lookup L.host .row) (.lookup cnt (.lit 0)) (e.atRow (L.index inv)) (.lit 0)

structure Fits (cnt inv : Bank) (w cap : ℕ) : Prop where
  host : L.host.Fits w cap
  low : L.low.Fits w cap
  stride : L.stride.Fits w cap
  count : cnt.Fits w cap
  inverse : inv.Fits w cap

theorem affine (first h r k : ℕ) :
    (⟨first,h,r,k⟩ : Layout).endAddress=first+(2*2^Nat.clog 2 (h*k)+2^Nat.clog 2 r):=rfl

theorem book_fits (cnt inv : Bank) (cntLow : cnt.Fits w L.first) (invLow : inv.Fits w L.first)
    (room : L.endAddress<2^w) : L.Fits cnt inv w L.endAddress := by
  have h : 0<L.pitch:=Nat.two_pow_pos _
  have n : 0<L.rawPitch:=Nat.two_pow_pos _
  have pos : L.first≤L.endAddress:=Nat.le_add_right ..
  have top : L.pitch<2^w ∧ L.rawPitch<2^w:=by dsimp [endAddress,size] at room;omega
  refine ⟨?_,?_,?_,⟨cntLow.1,cntLow.2.1,cntLow.2.2.trans pos⟩,⟨invLow.1,invLow.2.1,invLow.2.2.trans pos⟩⟩
  · exact ⟨h,top.1,by change L.first+L.pitch≤L.first+(2*L.pitch+L.rawPitch);omega⟩
  · exact ⟨h,top.1,by change L.first+L.pitch+L.pitch≤L.first+(2*L.pitch+L.rawPitch);omega⟩
  · exact ⟨n,top.2,by change L.first+2*L.pitch+L.rawPitch≤L.first+(2*L.pitch+L.rawPitch);omega⟩

theorem setup_run (m : Memory w) (room : L.endAddress<2^w) :
    (L.setup w).Exec m (L.mounted m) (4+10*L.size) ∧ CheapCode (L.setup w) ∧
      DescentStaticWordColumn.names (L.setup w)=15*(L.size+1) ∧
      ∀a,a<L.first ∨ L.endAddress≤a→L.mounted m a=m a := by
  refine ⟨DescentStaticWordColumn.mount L.first L.size L.literal m room,?_,DescentStaticWordColumn.names_mount ..,?_⟩
  · exact DescentStaticWordColumn.cheap w L.first L.literal L.size
  · exact DescentStaticWordColumn.frame L.first L.size L.literal m

theorem fits {cap : ℕ} {cnt inv : Bank} (safe : L.Fits cnt inv w cap) (e : Expr) (fit : e.Fits w cap) :
    (L.load cnt inv e).Fits w cap := by
  have atIndex : (L.index inv).Fits w cap:=⟨⟨safe.low,trivial⟩,safe.stride,safe.inverse,safe.host,trivial⟩
  have subst (f j : Expr) (fok : f.Fits w cap) (jok : j.Fits w cap) : (f.atRow j).Fits w cap:=by
    induction f <;> simp_all only [Expr.atRow,Expr.Fits] <;> tauto
  exact ⟨⟨safe.host,trivial⟩,⟨safe.count,trivial⟩,subst e _ fit atIndex,trivial⟩

theorem work (cnt inv : Bank) (e : Expr) :
    (L.load cnt inv e).work≤19+e.work*((L.index inv).work+1) := by
  have sub (f j : Expr) : (f.atRow j).work≤f.work*(j.work+1):=by
    induction f <;> simp only [Expr.atRow,Expr.work,Nat.add_mul,Nat.one_mul] at * <;> omega
  have bounded:=sub e (L.index inv)
  simp only [load,Expr.work]
  omega

theorem index_work (inv : Bank) : (L.index inv).work=25:=rfl

theorem load_work (cnt inv : Bank) (e : Expr) : (L.load cnt inv e).work≤19+26*e.work := by
  simpa only [index_work,Nat.reduceAdd,Nat.mul_comm] using L.work cnt inv e

/-- The two compact-rack coordinate projections and the sparse host stride
are mounted once. All logical operand expressions use these same three pages. -/
structure Books (m : Memory w) : Prop where
  host : ∀(v : Fin L.hosts) (j : Fin L.parts),m (L.host.base+(finProdFinEquiv (v,j)).val)=(v.val:Word w)
  low : ∀(v : Fin L.hosts) (j : Fin L.parts),m (L.low.base+(finProdFinEquiv (v,j)).val)=(j.val:Word w)
  stride : ∀i : Fin L.sparse,m (L.stride.base+i.val)=((i.val*L.parts:ℕ):Word w)

theorem books (m : Memory w) : L.Books (L.mounted m) := by
  have rows : L.hosts*L.parts≤L.pitch:=Nat.le_pow_clog (by decide) _
  have rr : L.sparse≤L.rawPitch:=Nat.le_pow_clog (by decide) _
  have read (j) (range : j<L.size) : L.mounted m (L.first+j)=(L.literal j:Word w):=
    DescentStaticWordColumn.read L.first L.size L.literal m range
  constructor
  · intro v j
    let i:=finProdFinEquiv (v,j)
    have live : i.val<L.pitch:=i.isLt.trans_le rows
    rw [show L.host.base+(finProdFinEquiv (v,j)).val=L.first+i.val from rfl,read _ (by dsimp [size];omega)]
    rw [literal,ite_eq_left live]
    simp [i,finProdFinEquiv_apply_val,Nat.add_mul_div_left _ _ (Fin.pos j),Nat.div_eq_of_lt j.isLt]
  · intro v j
    let i:=finProdFinEquiv (v,j)
    have live : i.val<L.pitch:=i.isLt.trans_le rows
    rw [show L.low.base+(finProdFinEquiv (v,j)).val=L.first+(L.pitch+i.val) by dsimp [low,i];omega,
      read _ (by dsimp [size];omega)]
    rw [literal,ite_eq_right (show ¬L.pitch+i.val<L.pitch by omega),ite_eq_left (show L.pitch+i.val<2*L.pitch by omega)]
    simp [i,finProdFinEquiv_apply_val,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]
  · intro i
    have live:=i.isLt
    rw [show L.stride.base+i.val=L.first+(2*L.pitch+i.val) by dsimp [stride];omega,
      read _ (by dsimp [size];omega)]
    simp [literal,show ¬2*L.pitch+i.val<L.pitch by omega,show ¬2*L.pitch+i.val<2*L.pitch by omega]

/-- The first unavailable dense ordinal and all subsequent racks emit literal zero. -/
theorem eval {cnt inv : Bank} (m : Memory w) (book : L.Books m) (f : Expr) {cap U : ℕ}
    (safe : L.Fits cnt inv w cap) (name : Fin U→Fin L.sparse) (count : m cnt.base=(U:Word w))
    (names : ∀i : Fin U,m (inv.base+i.val)=((name i).val:Word w))
    (countFits : U<2^w) (hostFits : L.hosts≤2^w) (invFits : U≤ inv.size)
    (v : Fin L.hosts) (c : Fin L.parts) :
    (L.load cnt inv f).eval m ((finProdFinEquiv (v,c)).val:Word w)=
      if h : v.val<U then f.eval m ((finProdFinEquiv (name ⟨_,h⟩,c)).val:Word w) else 0 := by
  let j:=finProdFinEquiv (v,c)
  have hf : j.val<L.pitch:=j.isLt.trans_le (Nat.le_pow_clog (by decide) _)
  have old : L.host.read m (j.val:Word w)=(v.val:Word w):=(bank_read _ _ hf safe.host).trans (book.host v c)
  have low : L.low.read m (j.val:Word w)=(c.val:Word w):=(bank_read _ _ hf safe.low).trans (book.low v c)
  have ct : cnt.read m ((0:ℕ):Word w)=(U:Word w):=by
    rw [bank_read cnt m (show 0<cnt.size from safe.count.1) safe.count,Nat.add_zero,count]
  change (if Comparison.lt.test (L.host.read m (j.val:Word w)) (cnt.read m ((0:ℕ):Word w)) then _ else _)=_
  rw [old,ct]
  simp only [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt (v.isLt.trans_le hostFits),Fin.val_cast_of_lt countFits,decide_eq_true_eq]
  by_cases h : v.val<U
  · let a:=name ⟨_,h⟩
    have ix : inv.read m (v.val:Word w)=(a.val:Word w):=(bank_read _ _ (h.trans_le invFits) safe.inverse).trans (names ⟨_,h⟩)
    have rawSize : L.sparse≤L.stride.size:=Nat.le_pow_clog (by decide) _
    have str : L.stride.read m (a.val:Word w)=((a.val*L.parts:ℕ):Word w):=
      (bank_read _ _ (a.isLt.trans_le rawSize) safe.stride).trans (book.stride a)
    rw [ite_eq_left h,dite_eq_left h,eval_atRow]
    change f.eval m ((L.low.read m (j.val:Word w))+(L.stride.read m (inv.read m (L.host.read m (j.val:Word w)))))=_
    rw [low,old,ix,str,←Nat.cast_add]
    exact congrArg (f.eval m) (congrArg (fun n : ℕ=>(n:Word w)) (by simp [a,finProdFinEquiv_apply_val,Nat.mul_comm]))
  · simp [h,Expr.eval]

end Layout

def dense (name : Fin used→Fin R) (data : Fin R→Fin G→Cell b) (h : Fin H) (g : Fin G) : Cell b :=
  if ok : h.val<used then data (name ⟨_,ok⟩) g else 0

theorem source (first : ℕ) (cnt inv : Bank) (input : Expr) (m : Memory w)
    (name : Fin used→Fin R) (values : Fin R→Fin G→Cell b) (words : Source input values M m) (cap : ℕ)
    (book : (⟨first,H,R,chunks G M⟩ : Layout).Books m)
    (safe : (⟨first,H,R,chunks G M⟩ : Layout).Fits cnt inv w cap)
    (count : m cnt.base=(used:Word w)) (names : ∀i : Fin used,m (inv.base+i.val)=((name i).val:Word w))
    (countFits : used<2^w) (hostFits : H≤2^w) (invFits : used≤ inv.size) :
    Source ((⟨first,H,R,chunks G M⟩ : Layout).load cnt inv input) (dense (H:=H) name values) M m := by
  rintro ⟨v,c⟩
  unfold row
  rw [Layout.eval _ m book input safe name count names countFits hostFits invFits v c]
  by_cases live : v.val<used
  · have valAt:=words (name ⟨_,live⟩,c)
    unfold row at valAt
    rw [dite_eq_left live,valAt]
    have eqData : data values (name ⟨_,live⟩,c)=data (dense name values) (v,c):=by
      unfold data
      apply congrArg (encode b M)
      funext l
      simp [dense,live]
    rw [eqData]
  · rw [dite_eq_right live]
    have zeros : data (dense (H:=H) name values) (v,c)=0:=by
      unfold data
      have empty : (fun j : Fin M=>if hj : c.val*M+j.val<G then dense (H:=H) name values v ⟨_,hj⟩ else 0)=
          fun _=>0:=by funext j;simp [dense,live]
      rw [empty]
      apply Fin.ext
      change (finFunctionFinEquiv (fun _ : Fin M=>(0:Cell b))).val=0
      simp []
    simp [zeros]

end
end Hierarchy.DescentResetDenseOperand

end OAI
