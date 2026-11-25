import OAI.Hierarchy.DescentCoarseCoordinates
import Mathlib.Data.Nat.Bitwise

namespace OAI
/-! # One original-order read for a pair of offsets after the selected linear permutation -/

namespace Hierarchy.DescentPlainTerminal
open DescentColonies DescentGL DescentIssuedFallbackPanel
open scoped Classical
noncomputable section

private theorem high_difference (x y u : ℕ) {w : ℕ} (xfit : x<2^w) (yfit : y<2^w) :
    (u*2^w+x) ^^^ (u*2^w+y)=x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor,Nat.mul_comm u (2^w),Nat.testBit_two_pow_mul_add _ xfit,
    Nat.testBit_two_pow_mul_add _ yfit]
  by_cases small : j<w
  · simp [small]
  · have le:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt small)
    simp [small,Nat.testBit_lt_two_pow (xfit.trans_le le),Nat.testBit_lt_two_pow (yfit.trans_le le)]

private theorem zmod_xor (a b : ZMod 2) : (a+b).val=a.val ^^^ b.val := by
  fin_cases a <;> fin_cases b <;> decide

theorem value_add (m : ℕ) (x y : Bits m) : value m (x+y)=value m x ^^^ value m y := by
  induction m with
  | zero=>simp [value]
  | succ m ih=>
    let xh:=headRows (Nat.le_succ m) x
    let yh:=headRows (Nat.le_succ m) y
    let xx:=x (Fin.last m)
    let yy:=y (Fin.last m)
    change 2*value m (xh+yh)+(xx+yy).val=(2*value m xh+xx.val) ^^^ (2*value m yh+yy.val)
    rw [ih,zmod_xor]
    apply Nat.eq_of_testBit_eq
    intro j
    have xxFit : xx.val<2^1:=ZMod.val_lt xx
    have yyFit : yy.val<2^1:=ZMod.val_lt yy
    change ((2^1)*(value m xh ^^^ value m yh)+(xx.val ^^^ yy.val)).testBit j=
      (((2^1)*value m xh+xx.val) ^^^ ((2^1)*value m yh+yy.val)).testBit j
    simp only [Nat.testBit_xor,
      Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow xxFit yyFit),
      Nat.testBit_two_pow_mul_add _ xxFit,Nat.testBit_two_pow_mul_add _ yyFit]
    by_cases low : j<1 <;> simp [low]

def xor {m : ℕ} (x y : Block m) : Block m :=
  ⟨x.val ^^^ y.val,Nat.xor_lt_two_pow x.isLt y.isLt⟩

theorem inverse_xor {m : ℕ} (L : Layout m) (x y : Block m) :
    xor ((rearrange L).symm x) ((rearrange L).symm y)=(rearrange L).symm (xor x y) := by
  let a:=(address m).symm x
  let b:=(address m).symm y
  have diff : address m (a+b)=xor x y := by
    calc
      address m (a+b)=xor (address m a) (address m b):=Fin.ext (value_add m a b)
      _=xor x y:=by simp [a,b]
  rw [←diff]
  change xor (address m (L.symm a)) (address m (L.symm b))=address m (L.symm ((address m).symm (address m (a+b))))
  rw [Equiv.symm_apply_apply,map_add]
  exact Fin.ext (value_add m (L.symm a) (L.symm b)).symm

theorem pivot_compare {a b z : ℕ} (diff : a ^^^ b=z) (nz : z≠0) :
    a<b ↔ b.testBit z.log2=true := by
  have atTop:=Nat.testBit_log2 nz
  have pivot : (a.testBit z.log2 ^^ b.testBit z.log2)=true := by
    simpa only [Nat.testBit_xor] using ((congrArg (fun t : ℕ=>t.testBit z.log2) diff).trans atTop)
  have later (k : ℕ) (gt : z.log2<k) : a.testBit k=b.testBit k := by
    have off:=Nat.testBit_lt_two_pow ((Nat.log2_lt nz).1 gt)
    rw [←diff,Nat.testBit_xor] at off
    simpa using off
  cases aBit : a.testBit z.log2 <;> cases bBit : b.testBit z.log2 <;> simp_all
  all_goals first
   | exact Nat.lt_of_testBit _ aBit bBit later
   | exact (Nat.lt_of_testBit _ bBit aBit (fun k hk=>(later k hk).symm)).le

/-- The displacement is computed once from the two bounded low offsets.
Each repeated coarse group reads the same one bit-position of its selected
inverse image. -/
def displacement {m c : ℕ} (L : Layout m) (u v : Block (m-c)) : Block m :=
  (rearrange L).symm ⟨u.val ^^^ v.val,(Nat.xor_lt_two_pow u.isLt v.isLt).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..))⟩

theorem inverse_order {m c : ℕ} (fits : c≤m) (L : Layout m) (hi : Block c) (u v : Block (m-c)) :
    (rearrange L).symm (join fits hi u)<(rearrange L).symm (join fits hi v) ↔
      u≠v ∧ ((rearrange L).symm (join fits hi v)).val.testBit (displacement L u v).val.log2=true := by
  by_cases equal : u=v
  · subst v;simp
  · rw [and_iff_right equal]
    let a:=(rearrange L).symm (join fits hi u)
    let b:=(rearrange L).symm (join fits hi v)
    let delta:=displacement L u v
    have linear:=inverse_xor L (join fits hi u) (join fits hi v)
    have combined : xor (join fits hi u) (join fits hi v)=⟨u.val ^^^ v.val,
        (Nat.xor_lt_two_pow u.isLt v.isLt).trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..))⟩ :=
      Fin.ext (high_difference _ _ hi.val u.isLt v.isLt)
    rw [combined] at linear
    have dif : a.val ^^^ b.val=delta.val:=congrArg Fin.val linear
    have nonzero : delta.val≠0 := by
      intro zero
      have alike : a.val=b.val := by
        apply Nat.eq_of_testBit_eq
        intro i
        have eqn:=congrArg (fun x : ℕ=>x.testBit i) (dif.trans zero)
        simpa using eqn
      have orig:=(rearrange L).symm.injective (Fin.ext alike)
      exact equal (by simpa using congrArg (low (c:=c)) orig)
    exact pivot_compare dif nonzero

end
end Hierarchy.DescentPlainTerminal

end OAI
