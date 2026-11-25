import OAI.Computability.IntegerMultiplication.Adic.Words
import OAI.Computability.IntegerMultiplication.Bits.Small -- fin codec

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open Code IntegerMultiplication.Port
variable {p : ℕ} [NeZero p]
private theorem positive_p (p : ℕ) [NeZero p] : 0<p := Nat.pos_of_ne_zero (NeZero.ne _)

def eqzip (x y : Raw p) :=
  (cutLists (ruler x,zipSafe (0:Fin p) (0:Fin p) (x,y))).1

theorem eqZipped (x y : Raw p) (h : x.length=y.length) :
    eqzip x y=x.zip y := by
  apply List.ext_getElem
  · simp [eqzip,cutLists,ruler_length,zipSafe,h]
  intro i e s
  have u : i<x.length := by simpa [h.symm] using s
  simp [eqzip,cutLists,ruler_length,zipSafe,u,List.getElem_append_left, show i<y.length by rwa [← h]]

@[fun_prop] theorem easy_eqzip {X : Type*} [Codec X] {x y : X → Raw p} (a : Easy x) (b : Easy y) :
    Easy (fun i => eqzip (x i) (y i)) := by
  apply (easy_cut (g:=fun i => (ruler (x i),zipSafe (0:Fin p) 0 (x i,y i))) ?_).fstCompose
  fun_prop

def linear (m n : ℕ) (s : Fin (m+n+1)) (d : Fin p × Fin p) :=
  m*d.1.val + n*d.2.val + s.val
omit [NeZero p] in
private theorem closed (m n) (s : Fin (m+n+1)) (d : Fin p × Fin p) :
    linear m n s d < p*(m+n+1) := by
  have k := d.1.isLt
  have l := d.2.isLt
  have q := s.isLt
  have h1 : m*(d.1.val+1) ≤ m*p := Nat.mul_le_mul_left _ k
  have h2 : n*(d.2.val+1) ≤ n*p := Nat.mul_le_mul_left _ l
  unfold linear
  rw [Nat.mul_add, Nat.mul_one] at h1 h2
  rw [Nat.mul_add,Nat.mul_add,Nat.mul_comm p m,Nat.mul_comm p n, Nat.mul_one p]
  omega

def combination (m n : ℕ) (d : Fin p × Fin p) (s : Fin (m+n+1)) :
    Fin (m+n+1) × List (Fin p) :=
  (⟨linear m n s d / p, by
      rw [Nat.div_lt_iff_lt_mul (positive_p p)]
      rw [mul_comm]; apply closed⟩,
    [⟨linear m n s d%p, Nat.mod_lt _ (positive_p _)⟩])

theorem hit (m n : ℕ) (d : Fin p × Fin p) (s : Fin (m+n+1)) :
    ∃ k t, combination m n d s=(k,[t]) ∧
      linear m n s d=t.val + p*k.val := by
  refine ⟨_,_,rfl,?_⟩
  exact (Nat.mod_add_div ..).symm

theorem run_lin (m n : ℕ) (x y : Raw p) (h : x.length=y.length) (s : Fin (m+n+1)) :
    let z := machine (combination m n) (x.zip y,s)
    z.1.length=x.length ∧
    m*code x+n*code y+s.val=code z.1+p^x.length*z.2.val := by
  induction x generalizing y s with
  | nil =>
    cases y <;> simp [code,machine_nil] at *
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons,Nat.add_left_inj] at h
      obtain ⟨k,t,e,d⟩ := hit m n (a,b) s
      obtain ⟨u,v,j⟩ : ∃ u v, machine (combination m n) (x.zip y,k)=(u,v) := ⟨_,_,rfl⟩
      specialize ih y h k
      rw [j] at ih
      simp only [List.zip_cons_cons,machine_cons,e,j,List.singleton_append,List.length_cons,code,ih.1,true_and,pow_succ, Nat.mul_comm _ p]
      dsimp only [linear] at d
      calc
       _ = m*a.val + n*b.val + s.val + p*(m*code x+n*code y) := by ring
       _ = _ := by
        rw [d]
        rw [show t.val+p*k.val + p*(m*code x+n*code y)=
          t.val+p*(m*code x+n*code y+k.val) by ring,ih.2]; ring -- ih let
def merge (m n) (a : Fin (m+n+1)) (i : Raw p × Raw p) :=
  machine (combination m n) (eqzip i.1 i.2,a)
@[fun_prop] theorem easy_merge {X : Type*} (m n) (u : Fin (m+n+1)) [Codec X] {k : X→Raw p × Raw p} (e : Easy k) :
    Easy (fun i => merge m n u (k i)) := by unfold merge; fun_prop

theorem merged (m n) (a : Fin (m+n+1)) (x y : Raw p) (h : x.length=y.length) :
    (merge m n a (x,y)).1.length=x.length ∧
    m*code x+n*code y+a.val=code (merge m n a (x,y)).1 + p^x.length*(merge m n a (x,y)).2.val := by
  simpa only [merge,eqZipped x y h] using run_lin m n x y h a
end Adic

end IntegerMultiplication
end Computability
end OAI
