import OAI.Computability.IntegerMultiplication.Carry.Shrink
import Mathlib.Data.Nat.Log

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Poly trim and logarithm. -/
namespace Carry
open Code Bits
-- reading little endian, trim
def tack (p : Word×Bool) : Word :=
  bif p.1.isEmpty && !p.2 then [] else p.2::p.1
def cut (t:Word) := t.reverse.foldl (fun x b=> tack (x,b)) []
@[fun_prop] theorem polyCut : Poly cut := by
  have a : Easy tack := by
    have i : Easy (fun p:Word×Bool=> p.1.isEmpty && !p.2) := by
      apply Easy.compose (f:=fun p:Word×Bool => (p.1.isEmpty,p.2)) (g:=fun p:Bool × Bool=>p.1 && !p.2)
      · exact (Easy.fst.compose (vacant _)).pair Easy.snd
      exact Easy.finite _
    unfold tack
    exact condition _ _ _ i (Easy.const _) (by fun_prop)
  have t := Poly.fold_left a.poly 4 1 (fun i l e=> ?_)
  exact (Easy.poly (f:=fun x:Word=> (x.reverse,([]:Word))) (by fun_prop)).compose t
  have v (x:Word) (y:Word) : size (y.foldl (fun x b=>tack (x,b)) x) ≤ size x+2*y.length := by
    induction y generalizing x with
    | nil=>simp
    | cons b l ih=>
      apply (ih (tack (x,b))).trans
      unfold tack; cases h:x.isEmpty && !b <;> simp [show size b=1 from rfl] <;> omega
  have h := v i.2 l
  have p := List.IsPrefix.length_le e
  rw [pow_one,size_prod]; have := Code.duration i.1; omega

@[simp] theorem cut_nil : cut []=[] := rfl
@[simp] theorem cuts (b l) : cut (b::l)=tack (cut l,b) := by simp [cut,List.foldl_append]

theorem cut_v (x:Word) :
    value (cut x)=value x ∧ (cut x).length≤x.length ∧
    (cut x = [] ∨ ∃ s,cut x=s++[true]) := by
  induction x with
  | nil=> exact ⟨rfl,le_rfl, Or.inl rfl⟩
  | cons b x ih=>
    obtain ⟨a,l,h|⟨s,h⟩⟩ := ih
    · cases b <;> simp [tack,h,h ▸ a.symm]
    have v : (s++[true]).isEmpty=false := by cases s <;> rfl
    simp only [← a, value_cons,cuts,tack,h,v,
      Bool.false_and, Bool.cond_false,List.length_cons]
    refine ⟨?_,by rw [h] at l; omega,Or.inr ⟨b::s,rfl⟩⟩
    trivial

theorem crown (s) : 2^s.length ≤ value (s++[true]) := by
  rw [value_append]; simp

theorem depth (n) :
    (born n).length ≤ Nat.clog 2 n+1 := by
  have v : ∀ n,born n=[] ∨ ∃ s,born n=s++[true] := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih=>
      rcases Nat.eq_zero_or_pos n with u | u
      · simp [u]
      obtain h|⟨s,h⟩ := ih _ (Nat.div_lt_self u (by decide:1<2))
      · have e := birthValue (n/2)
        rw [h,value_nil] at e
        have : n=1 := by omega
        simp [this,birth (by decide : 0<1)]
        exact ⟨[],rfl⟩
      rw [birth u,h]; exact Or.inr ⟨_::s,rfl⟩
  obtain h|⟨s,h⟩ := v n
  · simp [h]
  have j : 2^s.length≤n := by rw [← birthValue n,h]; exact crown s
  have t : 2^s.length≤2^Nat.clog 2 n := j.trans (Nat.le_pow_clog (by decide) _)
  simp [h,(Nat.pow_le_pow_iff_right (by decide :1<2)).mp t]

def dec_ (x:Word) : Word :=
  let i:= Bits.sub (x,[true])
  bif i.2 then [] else i.1
theorem dec_v (x) :
    value (dec_ x)=value x-1 := by
  unfold dec_
  dsimp only
  cases h:(Bits.sub (x,[true])).2
  · rw [Bool.cond_false,Bits.sub_val_le]
    · simp
    have u := Bits.sub_borrow x [true]
    rw [h] at u
    have t := u.not.mp Bool.noConfusion; exact le_of_not_gt t
  · simp only [Bool.cond_true,value_nil]
    have u := (Bits.sub_borrow x [true]).mp h
    simp at u
    omega

@[fun_prop] theorem easy_dec : Easy dec_ :=
  (show Easy (fun x:Word=>Bits.sub (x,[true])) from by fun_prop).compose
    (condition _ _ _ Easy.snd (Easy.const _) Easy.fst)

theorem measure (n) (x: Word) (h:value x=n-1) (a: x=[] ∨∃ s,x=s++[true]) :
    Nat.clog 2 n=x.length := by
  obtain h₀|⟨s,rfl⟩ := a
  · subst x
    simp only [List.length_nil]
    apply Nat.eq_zero_of_le_zero
    rw [Nat.clog_le_iff_le_pow (by decide)]
    change 0 = n-1 at h; omega
  apply Nat.le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    have p := value_lt (s++[true])
    omega
  · have p := crown s
    have e : s.length < Nat.clog 2 n := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by
      have t: 0< (2:ℕ)^s.length := by positivity
      omega)
    simpa using e

def light (x:Word) : Tally := ruler (cut (dec_ x))

@[fun_prop] theorem lightPoly : Poly light :=
  (easy_dec.poly.compose polyCut).compose (Easy.ruler Easy.identity).poly

theorem light_v (x) : light x = tally (Nat.clog 2 (value x)) := by
  rw [measure _ (cut (dec_ x)) ((cut_v _).1.trans (dec_v x)) (cut_v _).2.2]
  unfold light; simp [ruler,tally]
end Carry

end IntegerMultiplication
end Computability
end OAI
