import OAI.Hierarchy.DescentResetOriginHaloRAM
import OAI.Hierarchy.DescentResetOriginalSlots
import OAI.Hierarchy.ProtocolRAMRowChoiceFits
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # One-based old halo numbers on every real signed donor's compact predecessor -/
namespace Hierarchy.DescentResetSignedHaloMatrix
open DescentPackedColony DescentSIMDLookup DescentPackedZip DescentSortedRoster DescentResetOriginHaloRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H D S N w : ℕ}

def addr (H D base : ℕ) (s : Fin 2) : Bank:=⟨base+s.val*DescentResetOriginalSlots.stride (H*(D+1)),Nat.clog 2 (H*(D+1))⟩
def cells (H D : ℕ):=2*DescentResetOriginalSlots.stride (H*(D+1))
def init (H D : ℕ) (j : ℕ):=let step:=DescentResetOriginalSlots.stride (H*(D+1))
  if j<step then j/(D+1) else (j-step)%(D+1)
def key (H D base : ℕ) (s : Fin 2):=Expr.lookup (addr H D base s) .row
def term (H D S base : ℕ) (count owner roster : Bank) : Expr:=
  let h:=key H D base 0
  let slot:=key H D base 1
  let owner_:=Expr.lookup owner h
  let e:=chooseField (D+1) 0 (fun j=>(DescentResetOriginHaloRAM.op S roster j).atRow owner_) slot
  .branch .lt h (.lookup count (.lit 0)) (.op .add e (.lit 1)) (.lit 0)
def program (H D S w base out : ℕ) (count owner roster : Bank):=
  (DescentStaticWordColumn.program w base (init H D) (cells H D)).seq (scan w out (H*(D+1)) (term H D S base count owner roster))
def dst (H D S base out : ℕ) (count owner roster : Bank) (m : Memory w):=
  image out (H*(D+1)) (term H D S base count owner roster) (DescentStaticWordColumn.image base (init H D) m (cells H D))
def clock (H D S base : ℕ) (count owner roster : Bank):=
  4+10*cells H D+(4+H*(D+1)*(2*(term H D S base count owner roster).work+4))
def rank (p : Fin S→Fin D→Option (Fin S)) (home : Fin N→Fin S) (h : Fin H) (j : Fin (D+1)) :=
  if ok : h.val<N then let v:=home ⟨h.val,ok⟩; before (closed p) v ((closed p v j).getD v)+1 else 0

structure Room (H D S w base out : ℕ) (count owner roster : Bank) : Prop where
  countFit : count.Fits w base
  ownerFit : owner.Fits w base
  rosterFit : roster.Fits w base
  separate : base+cells H D≤out
  space : out+H*(D+1)<2^w
  hosts : H<2^w
  oldHosts : S<2^w
  degree : D+1<2^w
  extent : S*D≤roster.size

variable {base out : ℕ} {count owner roster : Bank}

theorem inputs (r : Room H D S w base out count owner roster) :
    let _coord:=fun s=>key H D base s
    (∀s,(addr H D base s).Fits w out) ∧ (term H D S base count owner roster).Fits w out:=by
  let n:=H*(D+1)
  have small : out<2^w:=(Nat.le_add_right ..).trans_lt r.space
  have early : base≤out:=(Nat.le_add_right ..).trans r.separate
  have room (s : Fin 2) : (addr H D base s).Fits w out:=by
    have fit:=Nat.mul_le_mul_right (DescentResetOriginalSlots.stride n) s.isLt
    rw [Nat.succ_mul] at fit
    have hi:(addr H D base s).base+(addr H D base s).size≤out:=by
      refine le_trans ?_ r.separate
      change base+s.val*DescentResetOriginalSlots.stride n+DescentResetOriginalSlots.stride n≤base+2*DescentResetOriginalSlots.stride n;omega
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (hi.trans_lt small),hi⟩
  have input (B : Bank) (fit : B.Fits w base) : B.Fits w out:=⟨fit.1,fit.2.1,fit.2.2.trans early⟩
  have point : (Expr.lookup owner (key H D base 0)).Fits w out:=⟨input _ r.ownerFit,room 0,trivial⟩
  exact ⟨room,⟨⟨room 0,trivial⟩,⟨input _ r.countFit,trivial⟩,⟨BoughtSockets.choose_fits_bound _ _ _ _ (fun j=>
    Calendar.CatalogueRows.fits_atRow _ _ (op_fits (H := S) roster j out (input _ r.rosterFit)) point) ⟨room 1,trivial⟩,trivial⟩,trivial⟩⟩

theorem any (r : Room H D S w base out count owner roster) (m : Memory w):
    (program H D S w base out count owner roster).Exec m (dst H D S base out count owner roster m) (clock H D S base count owner roster) ∧
    CheapCode (program H D S w base out count owner roster) ∧
    ∀a,(a<base ∨ base+cells H D≤a)→(a<out ∨ out+H*(D+1)≤a)→dst H D S base out count owner roster m a=m a:=by
  have cap : base+cells H D<2^w:=r.separate.trans_lt ((Nat.le_add_right ..).trans_lt r.space)
  refine ⟨Procedure.Exec.then (DescentStaticWordColumn.mount base (cells H D) (init H D) m cap)
      (scan_exec out (H*(D+1)) (term H D S base count owner roster) _ (inputs r).2 r.space),
    cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@scan_cheap _ _ _ _),?_⟩
  intro a first second;exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a second).trans (DescentStaticWordColumn.frame _ _ _ _ a first)

theorem read (r : Room H D S w base out count owner roster) (m : Memory w)
    (p : Fin S→Fin D→Option (Fin S)) (home : Fin N→Fin S) (maximum : N≤H) (fits : N≤owner.size)
    (countWord : m count.base=(N:Word w)) (ownerWord : ∀i,m (owner.base+i.val)=((home i).val:Word w))
    (edges : ∀v i,m (roster.base+(v.val*D+i.val))=(target (p v i):Word w)) (h : Fin H) (j : Fin (D+1)) :
    dst H D S base out count owner roster m (out+(h.val*(D+1)+j.val))=(rank p home h j:Word w):=by
  let n:=H*(D+1)
  let pitch:=DescentResetOriginalSlots.stride n
  let t : Fin n:=finProdFinEquiv (h,j)
  have tv : t.val=h.val*(D+1)+j.val:=by simp [t,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  let m₁:=DescentStaticWordColumn.image base (init H D) m (cells H D)
  let e:=term H D S base count owner roster
  have previous (a : ℕ) (lo : a<base) : m₁ a=m a:=DescentStaticWordColumn.frame _ _ _ _ a (.inl lo)
  have cnt:count.read m₁ ((0:ℕ):Word w)=(N:Word w):=by
    rw [bank_read count m₁ (i:=0) r.countFit.1 r.countFit,Nat.add_zero,
      previous _ (by have :=r.countFit.1;have :=r.countFit.2.2;omega),countWord]
  have stored (s : Fin 2) : (key H D base s).eval m₁ (t.val:Word w)=(if s=0 then h.val else j.val:ℕ):=by
    have small:t.val<pitch:=t.isLt.trans_le (DescentResetOriginalSlots.rows_le n)
    have divRow : t.val/(D+1)=h.val:=by
      rw [tv,Nat.mul_comm h.val (D+1),Nat.mul_add_div (Nat.succ_pos D),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
    have modRow : t.val%(D+1)=j.val:=by
      rw [tv,Nat.mul_comm h.val (D+1),Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt j.isLt]
    have low : init H D t.val=h.val:=by
      change (if t.val<pitch then t.val/(D+1) else (t.val-pitch)%(D+1))=_
      rw [ite_eq_left small,divRow]
    have high : init H D (pitch+t.val)=j.val:=by
      change (if pitch+t.val<pitch then (pitch+t.val)/(D+1) else (pitch+t.val-pitch)%(D+1))=_
      rw [ite_eq_right (by omega),show pitch+t.val-pitch=t.val by omega,modRow]
    change (addr H D base s).read m₁ (t.val:Word w)=_
    rw [bank_read (addr H D base s) m₁ (i:=t.val) small ((inputs r).1 s)]
    have idx:s.val*pitch+t.val<cells H D:=by
      have bound:=Nat.mul_le_mul_right pitch s.isLt
      rw [Nat.succ_mul] at bound;change _<2*pitch;omega
    change DescentStaticWordColumn.image base (init H D) m (cells H D) (base+s.val*pitch+t.val)=_
    rw [Nat.add_assoc,DescentStaticWordColumn.read base (cells H D) (init H D) m idx]
    fin_cases s <;> simp [low,high]
  rw [←tv]
  apply (ProtocolRAMGeneratedWrite.read_image out n e m₁ t).trans
  have guard : (key H D base 0).eval m₁ (t.val:Word w)=(h.val:Word w):=by simpa using stored 0
  have idx : ((key H D base 1).eval m₁ (t.val:Word w)).val=0+j.val:=by
    simp [stored,Nat.mod_eq_of_lt (j.isLt.trans r.degree)]
  have test : Comparison.lt.test (h.val:Word w) (N:Word w)=decide (h.val<N):=by
    simp [Comparison.test,Fin.lt_def,Nat.mod_eq_of_lt (h.isLt.trans r.hosts),Nat.mod_eq_of_lt (maximum.trans_lt r.hosts)]
  by_cases live : h.val<N
  · let i : Fin N:=⟨h.val,live⟩
    have owner_ : owner.read m₁ (h.val:Word w)=((home i).val:Word w):=by
      rw [bank_read _ _ (live.trans_le fits) r.ownerFit,previous _ (by have :=r.ownerFit.2.2;omega)];exact ownerWord i
    have read (v : Fin S) (z : Fin D) : m₁ (roster.base+(v.val*D+z.val))=(target (p v z):Word w):=by
      have span : v.val*D+z.val<S*D:=(Nat.add_lt_add_left z.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
      exact (previous _ (by have :=r.extent;have :=r.rosterFit.2.2;omega)).trans (edges v z)
    have choose:=eval_chooseField (D+1) 0 (fun j=>(op S roster j).atRow (.lookup owner (key H D base 0))) (key H D base 1) m₁ (t.val:Word w) j (by simpa using r.degree.le) idx
    rw [rank,dite_eq_left live]
    simp only [e,term,Expr.eval,guard,cnt,test,decide_eq_true live,ite_true,choose,eval_atRow,owner_,
      op_eval roster p j base m₁ r.rosterFit r.extent read r.oldHosts r.degree,Nat.cast_add,Nat.cast_one]; rfl
  · rw [rank,dite_eq_right live]
    simp only [e,term,Expr.eval,guard,cnt,test,decide_eq_false live]; rfl

end
end Hierarchy.DescentResetSignedHaloMatrix

end OAI
