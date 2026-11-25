import OAI.Computability.IntegerMultiplication.Strip.Dims
import OAI.Computability.IntegerMultiplication.Port.Span

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open Strip.Dims IntegerMultiplication.Port
abbrev Raw (p : ℕ) := List (Fin p)

variable {p l : ℕ}
-- tape orientation LSD first for algorithms
def code : Raw p → ℕ
| [] => 0
| a::c => a.val+p*code c
theorem cat (a b : Raw p) : code (a++b) = code a + p^a.length*code b := by
  induction a with
  | nil => simp [code]
  | cons f a ih =>
    simp [code,ih,pow_succ]; ring
theorem limit (c : Raw p) : code c < p^c.length := by
  induction c with
  | nil => simp [code]
  | cons a c ih =>
    simp only [code,List.length_cons,pow_succ, Nat.mul_comm (p^_)]
    have : p*(code c + 1) ≤ p*p^c.length := Nat.mul_le_mul_left _ ih
    rw [Nat.mul_add,Nat.mul_one] at this
    have := a.isLt
    omega
theorem uniq {x y : Raw p} (h : code x = code y) (e : x.length=y.length) :
    x=y := by
  induction x generalizing y with
  | nil => cases y <;> simp_all
  | cons d x ih =>
    cases y with
    | nil => simp at e
    | cons b y =>
      simp only [List.length_cons,Nat.add_left_inj] at e
      have a := d.isLt; have f := b.isLt
      rw [code,code] at h
      have t := congrArg (· % p) h
      rw [Nat.add_mul_mod_self_left,Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt f] at t
      have hz : d=b := Fin.ext t
      subst b
      congr 1
      apply ih _ e
      exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)

/-- Tape shape of one contiguous chunk of p-adic digits -/
def field (p : ℕ) : ℕ→Tape
| 0 => []
| l+1 => p::field p l
abbrev Block (p l : ℕ) := Pin (field p l)
def head {p l} (x : Fin p) (r : Block p l) : Block p (l+1) := node (x,r)

@[simp] theorem count : Fintype.card (Block p l) = p^l := by
  rw [population]
  induction l with
  | zero => rfl
  | succ l ih => rw [field, room_cons, ih, pow_succ']

def most {p} : {l : ℕ} → Block p l → Raw p
| 0,_ => []
| _+1,x => (look (n:=p) x).1::most (look (n:=p) x).2
def least (x : Block p l) := (most x).reverse
def number (x : Block p l) : ℕ := code (least x)

@[simp] theorem length (x : Block p l) : (most x).length=l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [most,List.length_cons, ih]
@[simp] theorem length' (x : Block p l) : (least x).length=l := by simp [least]

theorem distinct (p l) : Function.Injective (most (p:=p) (l:=l)) := by
  induction l with
  | zero => intro x y _; exact @Subsingleton.elim Unit _ x y
  | succ l ih =>
    rintro ⟨b,t⟩ ⟨a,k⟩ h -- dependent induction? defeq and recursor
    change b::most t = a::most k at h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 (ih h.2)

theorem number_cons (a : Fin p) (x : Block p l) :
    number (head a x) = number x + p^l*a.val := by
  unfold number least
  simp only [most,head,node,look,id_eq,List.reverse_cons]
  rw [cat,List.length_reverse,length,code,code]
  simp [id]

theorem number_lt [NeZero p] (x : Block p l) : number x<p^l := by
  simpa [number] using limit (least x)
theorem number_inj (p l) : Function.Injective (number (p:=p) (l:=l)) := by
  intro x y e
  apply distinct _ _
  apply List.reverse_injective
  exact uniq e (by simp)

instance power_inst [NeZero p] : NeZero (p^l) := ⟨Nat.ne_of_gt (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _)⟩
noncomputable section
def index (p l) [NeZero p] : Block p l ≃ Tower p l := Equiv.ofBijective
  (fun x => (number x : Tower p l)) (Fintype.bijective_iff_injective_and_card _ |>.mpr
    ⟨fun x y e => number_inj _ _ (by
      have hx := congrArg ZMod.val e
      simpa [ZMod.val_natCast_of_lt (number_lt _)] using hx),
      by rw [ZMod.card,count]⟩)
@[simp] theorem idx_nat (x : Block p l) [NeZero p] : index p l x = (number x:Tower p l) := rfl
@[simp] theorem decode (x : Tower p l) [NeZero p] :
    number ((index p l).symm x) = ZMod.val x := by
  rw [← ZMod.val_natCast_of_lt (number_lt _), ← idx_nat, Equiv.apply_symm_apply]
end
end Adic

end IntegerMultiplication
end Computability
end OAI
