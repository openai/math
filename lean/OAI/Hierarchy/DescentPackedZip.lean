import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # A physical two-column packed lookup for a short local update -/
namespace Hierarchy.DescentPackedZip
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a b c M H r w : ℕ}

def key (a b M : ℕ) : Cell (a*M) × Cell (b*M) ≃ Cell ((a+b)*M) :=
  finProdFinEquiv.trans (finCongr (by rw [Nat.add_mul,pow_add]))

theorem key_val (x : Cell (a*M)) (y : Cell (b*M)) :
    (key a b M (x,y)).val=y.val+2^(b*M)*x.val := rfl

def table (f : Cell a→Cell b→Cell c) (i : Cell ((a+b)*M)) : Cell (c*M) :=
  let (x,y):=(key a b M).symm i
  encode c M (fun j=>f ((encode a M).symm x j) ((encode b M).symm y j))

theorem table_data (f : Cell a→Cell b→Cell c) (empty : f 0 0=0)
    (x : Fin H→Fin r→Cell a) (y : Fin H→Fin r→Cell b) (p : Row H r M) :
    table f (key a b M (data x p,data y p))=data (fun v g=>f (x v g) (y v g)) p := by
  simp only [table,Equiv.symm_apply_apply,data]
  apply congrArg (encode c M)
  funext j
  by_cases live : p.2.val*M+j.val<r <;> simp [live,empty]

/-- The fixed scale table places the left operand beyond the right operand's
bits. Its addresses are common to every site, group and output row. -/
structure Tables where
  shift : Bank
  apply : Bank

def Tables.read (T : Tables) (x y : Expr) : Expr :=
  .lookup T.apply (.op .add y (.lookup T.shift x))

def code (T : Tables) (x y : Expr) (out H r M w : ℕ) := scan w out (H*chunks r M) (T.read x y)

def Static (T : Tables) (f : Cell a→Cell b→Cell c) (M : ℕ) (m : Memory w) : Prop :=
  (∀i : Cell (a*M),m (T.shift.base+i.val)=((2^(b*M)*i.val:ℕ):Word w)) ∧
    ∀i : Cell ((a+b)*M),m (T.apply.base+i.val)=((table f i).val:ℕ)

def Source (e : Expr) (x : Fin H→Fin r→Cell a) (M : ℕ) (m : Memory w) : Prop :=
  ∀p : Row H r M,e.eval m ((row H r M p).val:Word w)=((data x p).val:ℕ)

structure Fits (T : Tables) (x y : Expr) (a b M out w : ℕ) : Prop where
  left : x.Fits w out
  right : y.Fits w out
  shift : T.shift.Fits w out
  apply : T.apply.Fits w out
  shiftBits : T.shift.bits=a*M
  applyBits : T.apply.bits=(a+b)*M

theorem bank_read (B : Bank) (m : Memory w) {i out : ℕ} (small : i<B.size) (fit : B.Fits w out) :
    B.read m (i:Word w)=m (B.base+i) := by
  simp [Bank.read,Fin.val_cast_of_lt (small.trans fit.2.1),Nat.mod_eq_of_lt small]

theorem source_column (B : Bank) (out : ℕ) (fits : B.Fits w out) (m : Memory w)
    (x : Fin H→Fin r→Cell a) (room : H*chunks r M≤B.size)
    (installed : ∀p : Row H r M,m (B.base+(row H r M p).val)=((data x p).val:ℕ)) :
    Source (.lookup B .row) x M m := by
  intro p
  exact (bank_read B m ((row H r M p).isLt.trans_le room) fits).trans (installed p)

theorem read_data (T : Tables) (u v : Expr) (out : ℕ) (fit : Fits T u v a b M out w)
    (f : Cell a→Cell b→Cell c) (empty : f 0 0=0) (m : Memory w) (fixed : Static T f M m)
    (x : Fin H→Fin r→Cell a) (y : Fin H→Fin r→Cell b)
    (src : Source u x M m) (dst : Source v y M m) :
    Source (T.read u v) (fun pos g=>f (x pos g) (y pos g)) M m := by
  intro p
  have sh : (data x p).val<T.shift.size := by simp [Bank.size,fit.shiftBits]
  let i:=key a b M (data x p,data y p)
  have ii : i.val<T.apply.size := by simp [Bank.size,fit.applyBits]
  change T.apply.read m ((v.eval m _)+T.shift.read m (u.eval m _))=_
  rw [src p,dst p,bank_read T.shift m sh fit.shift,fixed.1,←Nat.cast_add]
  change T.apply.read m (i.val:Word w)=_
  rw [bank_read T.apply m ii fit.apply,fixed.2]
  exact congrArg (fun z : Cell (c*M)=>(z.val:Word w)) (table_data f empty x y p)

theorem spec (T : Tables) (u v : Expr) (out : ℕ) (fit : Fits T u v a b M out w)
    (room : out+H*chunks r M<2^w) (f : Cell a→Cell b→Cell c) (empty : f 0 0=0)
    (x : Fin H→Fin r→Cell a) (y : Fin H→Fin r→Cell b) :
    (code T u v out H r M w).Spec
      (fun m=>Static T f M m ∧ Source u x M m ∧ Source v y M m)
      (fun before after=>after=image out (H*chunks r M) (T.read u v) before ∧
        ∀p : Row H r M,after (out+(row H r M p).val)=((data (fun z j=>f (x z j) (y z j)) p).val:ℕ))
      (4+(H*chunks r M)*(2*(T.read u v).work+4)) ∧ CheapCode (code T u v out H r M w) := by
  refine ⟨?_,scan_cheap w out (H*chunks r M) (T.read u v)⟩
  have fields : (T.read u v).Fits w out := by simp [Tables.read,Expr.Fits,fit.left,fit.right,fit.apply,fit.shift]
  intro P N K mach pc reg pub exit rom regs cfg m start pre
  obtain ⟨time,ticks,done,after,ran,ended,mem⟩ := scan_exec out (H*chunks r M) (T.read u v) m fields
    room mach pc reg pub exit rom regs cfg m start rfl
  refine ⟨time,ticks,done,after,ran,ended,mem,?_⟩
  intro p
  rw [mem]
  have ip:=(row H r M p).isLt
  simpa [image,fillSegment,show out≤out+(row H r M p).val ∧
    out+(row H r M p).val<out+H*chunks r M by omega,Nat.cast_add] using
    read_data T u v out fit f empty m pre.1 x y pre.2.1 pre.2.2 p

theorem work (T : Tables) (u v : Expr) : (T.read u v).work=u.work+v.work+11 := by
  change (v.work+(u.work+5)+1)+5=_
  omega

/-- Both public tables fit the same shared half-word ROM ceiling. -/
theorem tariff (a b c w : ℕ) :
    let M:=lanes w (max (a+b) c)
    2^(a*M)+2^((a+b)*M)≤2*2^(w/2) := by
  dsimp only
  have combined:=rom_entries (a+b) c w
  have first:2^(a*lanes w (max (a+b) c))≤2^((a+b)*lanes w (max (a+b) c)) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  omega

end
end Hierarchy.DescentPackedZip

end OAI
