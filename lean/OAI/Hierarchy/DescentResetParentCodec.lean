import OAI.Hierarchy.DescentResetCompactParent

namespace OAI
/-! # Arithmetic coding of a reset-parent comparison and its measured zero bit -/
namespace Hierarchy.DescentResetParentCodec
open DescentResetCompactParent DescentHostDirectory
open scoped Classical
noncomputable section
variable {α β : Type}

structure Codec (A : Type) where
  cap : ℕ
  write : A→Fin cap
  read : Fin cap→Option A
  correct : ∀v,read (write v)=some v

def digit (n : ℕ) : Codec (Fin n) := ⟨n,id,some,fun _=>rfl⟩

def pair (A : Codec α) (B : Codec β) : Codec (α×β) where
  cap:=A.cap*B.cap
  write:=fun v=>finProdFinEquiv (A.write v.1,B.write v.2)
  read:=fun z=>do
    let fields:=finProdFinEquiv.symm z
    let a←A.read fields.1
    let b←B.read fields.2
    pure (a,b)
  correct:=by rintro ⟨u,v⟩;simp [A.correct,B.correct]

def tagged (A : Codec α) (B : Codec β) : Codec (α⊕β) where
  cap:=A.cap+B.cap
  write:=fun v=>finSumFinEquiv (v.map A.write B.write)
  read:=fun z=>(finSumFinEquiv.symm z).elim (fun a=>(A.read a).map Sum.inl) (fun b=>(B.read b).map Sum.inr)
  correct:=by intro v;cases v <;> simp [A.correct,B.correct]

private theorem bounds {r d j : ℕ} (hit : (d,j)∈codes r) : d≤r ∧ j<2^d := by
  induction r with
  | zero=>
    simp only [codes,Finset.mem_singleton,Prod.mk.injEq] at hit
    obtain ⟨rfl,rfl⟩:=hit;decide
  | succ r ih=>
    rcases Finset.mem_union.mp hit with prev|here
    · have h:=ih prev;exact ⟨h.1.trans (Nat.le_succ _),h.2⟩
    · obtain ⟨y,hy,eqn⟩:=Finset.mem_image.mp here
      obtain ⟨hd,hj⟩:=Prod.mk.inj eqn
      subst d;subst j
      exact ⟨le_rfl,Finset.mem_range.mp hy⟩

private def rectangle (r : ℕ) (v : Label r) : Fin (r+1)×Fin (2^r) :=
  let h:=bounds v.property
  (⟨v.val.1,Nat.lt_succ_of_le h.1⟩,⟨v.val.2,h.2.trans_le (Nat.pow_le_pow_right (by decide) h.1)⟩)

def interval (r : ℕ) : Codec (Label r) where
  cap:=(r+1)*2^r
  write:=fun u=>finProdFinEquiv (rectangle r u)
  read:=fun t=>
    let slots : Fin (r+1)×Fin (2^r):=finProdFinEquiv.symm t
    if valid : slots.2.val<2^slots.1.val then some ⟨(slots.1.val,slots.2.val),mem_codes (Nat.le_of_lt_succ slots.1.isLt) valid⟩ else none
  correct:=by
    intro u
    simp only [Equiv.symm_apply_apply,rectangle]
    rw [dite_eq_left (bounds u.property).2]

theorem interval_write_val {r : ℕ} (q : DescentResetCompactParent.Label r) :
    ((interval r).write q).val=q.val.1*2^r+q.val.2:=by
  simp only [interval,finProdFinEquiv_apply_val,rectangle]
  ring

def site (H r Y : ℕ) : Codec (SiteWord H r Y) :=
  tagged (pair (digit H) (interval r)) (pair (digit H) (pair (interval r) (digit (Y+1))))

def word (H r Y L cap links program : ℕ) : Codec (Word H r Y L cap links program) :=
  let s:=site H r Y
  tagged (pair (digit 2) (pair (digit L) (pair (digit cap) (digit cap))))
    (tagged s (tagged (pair s (digit links)) (pair (digit 2) (pair s (digit program)))))

def capCount (H r Y L cap links program : ℕ) :=
  let interval:=(r+1)*2^r
  let site:=H*interval+H*(interval*(Y+1))
  2*(2*(L*(cap*cap))+(site+(site*links+2*(site*program))))

section
variable {H r Y L cap links program : ℕ}
local notation "A" => Word H r Y L cap links program
local notation "format" => pair (digit 2) (word H r Y L cap links program)

def number (zero : Bool) (v : A) := ((format).write (if zero then 1 else 0,v)).val

theorem number_lt (zero : Bool) (v : A) : number zero v<capCount H r Y L cap links program :=
  ((format).write (if zero then 1 else 0,v)).isLt

def seen (z : ℕ) : Option (Fin 2×A) :=
  if fits : z<(format).cap then (format).read ⟨z,fits⟩ else none

theorem read_number (zero : Bool) (v : A) : seen (number zero v)=some (if zero then 1 else 0,v) := by
  unfold seen number
  rw [dite_eq_left ((format).write _).isLt]
  exact (format).correct _

/-- Both live lane labels are finite. The zero bit is taken from the
receiver of the query after decoding its original four-part tag. -/
def before (base : ℕ) (left right : ℕ) : Bool :=
  match seen (H:=H) (r:=r) (Y:=Y) (L:=L) (cap:=cap) (links:=links) (program:=program) left,
      seen (H:=H) (r:=r) (Y:=Y) (L:=L) (cap:=cap) (links:=links) (program:=program) right with
  | some (_,x),some (z,y)=>decide (Word.before base (decide (z.val=1)) x y)
  | _,_=>false

theorem before_number (base : ℕ) (unused zero : Bool) (x y : A) :
    before (H:=H) (r:=r) (Y:=Y) (L:=L) (cap:=cap) (links:=links) (program:=program) base
      (number unused x) (number zero y)=decide (Word.before base zero x y) := by
  simp only [before, read_number]
  cases zero <;> rfl

end
end
end Hierarchy.DescentResetParentCodec

end OAI
