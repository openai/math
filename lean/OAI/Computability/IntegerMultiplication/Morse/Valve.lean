import OAI.Computability.IntegerMultiplication.Halo.Minor

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Net.Tensor Strip Loom Adic Dusk Grid Axon Finset
open Code Bits Hook Matrix
variable {k w n:ℕ} (p:ℕ) (q:Bits.Word) (b:ℕ→Grain w)
abbrev Dn (k:ℕ):=Axon.Scr (Fin 1) k
abbrev solo (x:Face k):Dn k:=fun _=>x
abbrev oneE {X:Type} : X≃(Fin 1→X) where
  toFun x:=fun _=>x
  invFun x:=x 0
  left_inv _:=rfl
  right_inv x:=by ext i; change x 0=x i; congr; exact Subsingleton.elim _ _

abbrev cls (k w:ℕ):=Face k→Grain w
abbrev set (i:Fin k)(z: B)(v:Face k) :Face k:=Function.update v i z

def wage (u:Grain w)(y:Grain w):Grain w:=
  Grid.launch (u,tally p,Dusk.mark y)

abbrev met (i:Fin k) (v:Face k):ℕ:=
  2^i.val * (Bits.value q * Axon.pin (v i)*Axon.beyond v i)
noncomputable def go (i:Fin k) (x:cls k w) (v:Face k):Grain w:=
  wage p (x (set i 0 v)+ (Walsh.F (v i) 1)* x (set i 1 v)) (b ((met q i v)%2^k))

private theorem bitSum (f:B→Grain w): ∑ i:B,f i=f 0+f 1 :=
  Fin.sum_univ_two f

theorem identity (i:Fin k) (x : cls k w) :
    effort p (fun _:Fin 1=>q) b i (x ∘ oneE.symm)= go p q b i x ∘ oneE.symm := by
  classical
  funext t
  let v:= t 0
  change launch ((zoom i F *ᵥ (x ∘ oneE.symm)) t,_,mark (b _))= wage p (x _ +(F (v i) 1)*x _) (b ((met q i v)%2^k))
  unfold wage
  have U : θ i (value ∘ fun _:Fin 1=>q) t=met q i v :=
    congrArg (fun s=>2^i.val*s) (Finset.sum_congr (rfl : (Finset.univ:Finset (Fin 1))=_) (fun j _=>rfl) |>.trans (Fin.sum_univ_succ _ |>.trans (by simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero]; rfl)))
  rw [U]
  have e : (zoom i F *ᵥ (x ∘ oneE.symm)) t=x (set i 0 v)+ F (v i) 1*x (set i 1 v) := by
    rw [Axon.retinal]
    let f (z:Addr (Fin 1)):= mat (fun _=> F) (who i t) z*(x ∘ oneE.symm) (replaceAt i t z)
    change ∑ z,f z=_
    rw [← (oneE (X:=B)).sum_comp f,bitSum]
    have h (z:B): f (oneE z)=F (v i) z*x (set i z v):= by
      unfold f
      rw [Net.Tensor.app, Fin.prod_univ_succ]
      simp only [Finset.univ_eq_empty, Finset.prod_empty,mul_one]; rfl
    rw [h,h,show (F (v i) 0:Grain w)=1 from by unfold Walsh.F; simp]
    rw [one_mul]
  rw [e]; rfl

variable (x:cls (k+1) w)
abbrev pre (c:B)(a:Face k):Face (k+1):=branch (c,a)
abbrev stepB (c:B):= fun z:Face k=>x (pre c z)
theorem rewrite_s (c:B) (a:Face k) (z:B) (i:Fin k):
    set i.succ z (pre c a)=pre c (set i z a):= by
  funext j
  refine Fin.cases ?_ (fun u=> ?_) j
  · simp only [set,Function.update_of_ne (Ne.symm i.succ_ne_zero),pre,branch,first_j]
  by_cases h:u=i
  · subst u; simp [set,pre,branch]
  · simp only [set,Function.update_of_ne (fun s=> h (Fin.succ_inj.mp s)),pre,branch,tail_j,Function.update_of_ne h]
theorem rewrite_f (c:B) (a:Face k)(z:B):
    set 0 z (pre c a)=pre z a:= by
  funext j
  refine Fin.cases ?_ (fun u=> ?_) j
  · simp [set,pre,branch]
  simp only [set,Function.update_of_ne (Fin.succ_ne_zero _),pre,branch,tail_j]

theorem met_r (v:Face (k+1))(i:Fin k):
    (met q i.succ v)%2^(k+1) = 2*((met q i (stem v))%2^k) := by
  unfold met
  rw [beyond_s,Fin.val_succ,pow_succ,pow_succ']
  set z:= Bits.value q * Axon.pin (v i.succ)*beyond (stem v) i
  change (2^i.val*2*z)%(2*2^k)=_
  rw [Nat.mul_comm _ 2,Nat.mul_assoc,Nat.mul_mod_mul_left]
abbrev doubleBank {α:Type} (b:ℕ→α)(i:ℕ):=b (2*i)
theorem goes_s (c:B)(i:Fin k):
    stepB (go p q b i.succ x) c=go p q (doubleBank b) i (stepB x c) := by
  funext z
  change wage p _ (b ((met q i.succ (pre c _))%2^(k+1)))= wage p _ (b _)
  rw [met_r,show stem (pre c z)=z from stem_b _]
  congr 1
  rw [rewrite_s,rewrite_s,show pre c z i.succ=z i from tail_j _ _ i]

abbrev get_ (c:B)(z:Face k) :=
  b ((Bits.value q*pin c*Axon.bold z)%2^(k+1))
noncomputable def blink (c:B) (z:Face k):Grain w :=
  wage p (x (pre 0 z) + F c 1 * x (pre 1 z)) (get_ q b c z)

theorem goes0 (c:B):
    stepB (go p q b 0 x) c=blink p q b x c := by
  funext z
  unfold stepB go blink met get_
  rw [rewrite_f,rewrite_f,beyond_b]
  rw [show pre c z 0 = c from first_j ..,show stem (pre c z)=z from stem_b _]
  simp
end Morse

end IntegerMultiplication
end Computability
end OAI
