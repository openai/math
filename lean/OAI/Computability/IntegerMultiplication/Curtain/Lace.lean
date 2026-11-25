import OAI.Computability.IntegerMultiplication.Net.Spectrum

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain
open Net.Walsh Net.Tensor Finset Matrix
variable (J F U : Type)
abbrev Sigs := F ⊕ U×B
abbrev Pin := Sigs F U ≃ J
variable {J F U}
namespace Pin
variable (p : Pin J F U)
-- position perm
abbrev alone (k : F) := p (Sum.inl k)
abbrev mate (k : U) (q : B) := p (Sum.inr (k,q))
def resp (k : Sigs F U) : Sigs F U :=
  Sum.elim Sum.inl (fun (k:U×B)=> Sum.inr (k.1,k.2+1)) k

def pos : Equiv.Perm J :=
  let d : Equiv.Perm (Sigs F U) := {
    toFun := resp
    invFun := resp
    left_inv k := by
      rcases k with k|⟨k,b⟩
      · rfl
      change Sum.inr (k,b+1+1)= _
      rw [add_assoc,show (1:B)+1=0 by decide,add_zero]
    right_inv k := by
      cases k with
      | inl => rfl
      | inr x =>
        obtain ⟨x,b⟩ := x
        change Sum.inr (x,b+1+1) = _
        rw [add_assoc,show (1:B)+1=0 by decide,add_zero] }
  p.symm.trans (d.trans p)
@[simp] theorem still k : pos p (alone p k)=alone p k := by
  unfold pos alone
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl
@[simp] theorem spill k b : pos p (mate p k b)= mate p k (b+1) := by
  unfold pos mate
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl
@[simp] theorem neutral j : pos p (pos p j)=j :=
  (pos p).symm_apply_apply j

def ret (x : Addr J) : Addr J := x ∘ pos p
def dx (x : Addr J) (k : F) := x (alone p k)
def lo (x : Addr J) (k : U) := x (mate p k 0)
def hi (x : Addr J) (k : U) := x (mate p k 1)
theorem dx_s x k : dx p (ret p x) k = dx p x k := by simp [dx,ret]
theorem lo_h x k : lo p (ret p x) k = hi p x k := by simp [lo,ret,hi]
theorem hi_l x k : hi p (ret p x) k = lo p x k := by
  simp [hi,ret,lo,show (1:B)+1=0 by decide]
@[simp] theorem retain x : ret p (ret p x) = x := by ext; simp [ret]
theorem ret_add (x y : Addr J) : ret p (x+y)=ret p x+ret p y := rfl

variable [Fintype J] [DecidableEq J] [Fintype F] [Fintype U]
def q (x : Addr J) : Clock :=
  (∑ k,digit (dx p x k)) + ∑ k, exp2 (lo p x k * hi p x k)
omit [Fintype J] [DecidableEq J] in
theorem q_s x : q p (ret p x) = q p x := by simp [q,dx_s,lo_h,hi_l,mul_comm]
omit [DecidableEq J] in
theorem p_dot (x y : Addr J) :
    x ⬝ᵥ y = (∑ k,dx p x k * dx p y k)+
             ∑ k,(lo p x k * lo p y k+hi p x k * hi p y k) := by
  let f := fun j => x j*y j
  unfold dotProduct
  change ∑ i, f i = _
  rw [← p.sum_comp f,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp_rw [duo] -- duo B
  rfl
omit [DecidableEq J] in
theorem p_ret (x y: Addr J) :
    x ⬝ᵥ ret p y = ret p x ⬝ᵥ y := by
  rw [p_dot p,p_dot p]
  simp_rw [dx_s,lo_h,hi_l]
  simp only [add_comm (lo _ _ _ * hi _ _ _)]
omit [DecidableEq J] in
theorem quadr (x y : Addr J) :
    q p (x+y) = q p x + q p y + exp2 (x ⬝ᵥ ret p y) := by
  rw [q,q,q,p_dot p]
  simp_rw [dx_s,lo_h,hi_l,map_add,map_sum]
  have d (i : F) : dx p (x+y) i = dx p x i+dx p y i := rfl
  have h (i:U) : hi p (x+y) i = hi p x i+hi p y i := rfl
  have l (i:U) : lo p (x+y) i = lo p x i+lo p y i := rfl
  simp_rw [d,h,l, polar,add_mul,mul_add,map_add, Finset.sum_add_distrib,mul_comm (lo p y _)]
  abel

-- reindex address by pairs
abbrev Twin : Type := B×B

def chooseB (k:Twin) (b:B) : B := if b=0 then k.1 else k.2
def tile (x : Addr J) : Addr F × (U→Twin) := (dx p x,fun k=> (lo p x k,hi p x k))
def spin (x : Addr F × (U→Twin)) : Addr J :=
  Sum.elim x.1 (fun v=> chooseB (x.2 v.1) v.2) ∘ p.symm
omit [Fintype J] [DecidableEq J] [Fintype F] [Fintype U] in
theorem spin1 x k : dx p (spin p x) k = x.1 k := by simp [spin,dx,alone]
omit [Fintype J] [DecidableEq J] [Fintype F] [Fintype U] in
theorem spin_l x k : lo p (spin p x) k = (x.2 k).1 := by simp [spin,lo,mate,chooseB]
omit [Fintype J] [DecidableEq J] [Fintype F] [Fintype U] in
theorem spin_h x k : hi p (spin p x) k = (x.2 k).2 := by simp [spin,mate,hi,chooseB]
def twin : Addr J ≃ Addr F × (U→Twin) where
  toFun := tile p
  invFun := spin p
  left_inv x := by
    funext i
    obtain ⟨i,rfl⟩ := p.surjective i
    cases i with
    | inl i => exact spin1 p _ _
    | inr v =>
      rcases v with ⟨i,b⟩
      rcases bit_value b with e|e
      · subst b; exact spin_l p _ _
      subst b; exact spin_h p _ _
  right_inv x := by
    exact Prod.ext (funext (spin1 p x)) (funext fun k=> Prod.ext (spin_l p x k) (spin_h p x k))

end Pin
-- methods dot and W
variable {R:Type} [CommRing R] (c : Quarter R)
namespace Pin
variable [Fintype J] [DecidableEq J] [Fintype F] [Fintype U] [DecidableEq F] [DecidableEq U]
variable (p : Pin J F U)
abbrev D (a : Addr J) : R := c.ph (q p a)
def G : R := ∑ x,D c p x
theorem gauss_lace :
    G c p = (1+c.i)^Fintype.card F*(2:R)^Fintype.card U := by
  rw [G,← (twin p).symm.sum_comp (D c p)]
  have e (v : Addr F × (U→Twin)) :
      D c p ((twin p).symm v) = (∏ i,c.ph (digit (v.1 i)))*∏ i,c.ph (exp2 ((v.2 i).1*(v.2 i).2)) := by
    unfold D q
    simp only [c.of_add,c.of_sum]
    change (∏ i : F,c.ph (digit (dx p (spin p v) i)))* (_)= _
    simp only [spin1]
    change _ * (∏ i,c.ph (exp2 (lo p (spin p v) i * hi p (spin p v) i))) = _
    simp only [spin_l,spin_h]
  rw [Fintype.sum_prod_type]
  simp_rw [e]
  rw [← Finset.sum_mul_sum]
  rw [← Fintype.prod_sum (fun (_:F) (b:B)=> c.ph (digit b)),← Fintype.prod_sum (fun (_:U) (x:Twin)=> c.ph (exp2 (x.1*x.2)))]
  have a : (∑ b:B,c.ph (digit b))=1+c.i := by
    rw [duo,show digit 0 = 0 by decide,show digit 1=1 by decide]; simp
  have r : (∑ x:Twin,c.ph (exp2 (x.1*x.2)))=(2:R) := by
    rw [Fintype.sum_prod_type]
    simp_rw [duo]
    simp only [mul_zero,mul_one,map_zero,c.null,c.shift,Quarter.sing]
    ring
  simp only [r,a]
  simp
end Pin
end Curtain

end IntegerMultiplication
end Computability
end OAI
