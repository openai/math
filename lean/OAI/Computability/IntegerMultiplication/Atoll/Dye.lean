import OAI.Computability.IntegerMultiplication.Atoll.Braid
import OAI.Computability.IntegerMultiplication.Staff.Tabs

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Strip Staff
variable (f k r:ℕ)
def go (n:ℕ) :=
  if n < r then f*k+n else (f-1-(n-r)/k)*k+(n-r)%k
def undo_ (n:ℕ):=
  if n < f*k then r+((f-1-n/k)*k+n%k) else n-f*k
private theorem divv {a b c:ℕ} (e:a<c):
    (a+c*b)/c=b ∧ (a+c*b)%c=a := by
  have z:0<c:=by omega
  rw [Nat.add_mul_div_left _ _ z,Nat.add_mul_mod_self_left]
  simp [Nat.div_eq_of_lt e,Nat.mod_eq_of_lt e]

private theorem d1 (p: Fiber f k r):
    go f k r (Aspot f k r p).val=(Bspot f k r p).val:= by
  cases p with
  | inl p=>
    change go _ _ _ p.val=f*k+p.val
    simp [go,p.isLt]
  | inr p=>
    obtain ⟨i,j⟩:=p
    change go f k r (r+(j.val+k*i.rev.val))=j.val+k*i.val
    unfold go
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    rw [(divv (b:=i.rev.val) j.isLt).1,(divv (b:=i.rev.val) j.isLt).2]
    rw [show f-1-i.rev.val=i.val by change f-1-(f-(i.val+1))=i.val; have := i.isLt; omega];ring
private theorem d2 (p:Fiber f k r):
    undo_ f k r (Bspot f k r p).val=(Aspot f k r p).val := by
  cases p with
  | inl p=>
    change undo_ _ _ _ (f*k+p.val)=p.val
    simp [undo_]
  | inr p=>
    obtain ⟨i,j⟩:=p
    change undo_ f k r (j.val+k*i.val)=r+(j.val+k*i.rev.val)
    unfold undo_
    have h:=i.isLt; have R:=j.isLt
    have L : j.val+k*i.val<f*k:=by nlinarith [Nat.mul_le_mul_left k (show i.val+1≤ f from h)]
    rw [ite_eq_left L,(divv (b:=i.val) R).1,(divv (b:=i.val) R).2]
    rw [show f-1-i.val=i.rev.val by change _ = f-(i.val+1); omega];ring
private theorem followGo (p:Fin (Mbit f k r)):
    go f k r p.val=(orderMW f k r p).val := by
  obtain ⟨j,rfl⟩:=(Aspot f k r).surjective p
  unfold orderMW
  rw [Equiv.trans_apply,Equiv.symm_apply_apply]
  exact d1 ..
private theorem followUndo (p:Fin (Mbit f k r)):
    undo_ f k r p.val=((orderMW f k r).symm p).val := by
  obtain ⟨j,rfl⟩:=(Bspot f k r).surjective p
  unfold orderMW
  rw [Equiv.symm_trans_apply,Equiv.symm_apply_apply]
  exact d2 ..
variable {I:Type}{p:Strip.Regime I}{x y z:I→ℕ}(a:Realizes p x)(b:Realizes p y)(c:Realizes p z)
include a b c
theorem dyed :
    let q i:=orderMW (x i) (y i) (z i)
    p.Has (fun i=>Curtain.paint (q i)) ∧ p.Has (fun i=>Curtain.paint (q i).symm):= by
  let n i := Mbit (x i) (y i) (z i)
  have A:Realizes p n:=c.plus (a.times b)
  let r:= signal n A
  let X:= landing n A x a
  let Y:=landing n A y b
  let Z:=landing n A z c
  let M:=floor_ n A
  constructor
  · apply harvest n A
    simp_rw [← followGo]
    let D:=M.minused Z
    exact Realizes.select ((X.times Y).plus M) ((((X.minused (.fix 1)).minused (D.dividing Y)).times Y).plus (D.rem Y))
      (M.below Z)
  apply harvest n A
  simp_rw [← followUndo]
  exact Realizes.select (Z.plus ((((X.minused (.fix 1)).minused (M.dividing Y)).times Y).plus (M.rem Y)))
    (M.minused (X.times Y)) (M.below (X.times Y))

end Atoll

end IntegerMultiplication
end Computability
end OAI
