import OAI.Computability.IntegerMultiplication.Adic.Divide

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open IntegerMultiplication.Port Code
variable {p : ℕ} [NeZero p]

def Holds (j : ℕ) (x : Raw p) (a : Tower p j) := x.length=j ∧ (code x:Tower p j)=a
namespace Holds
variable {j : ℕ} {x y : Raw p} {a b : Tower p j}
omit [NeZero p] in
theorem length (h : Holds j x a) : x.length=j := h.1
omit [NeZero p] in
theorem reads (h : Holds j x a) : (code x:Tower p j)=a := h.2
omit [NeZero p] in
theorem single (h : Holds j x a) (d : Holds j y a) : x=y := by
  have p0 := congrArg (ZMod.val (n:=p^j)) (h.2.trans d.2.symm)
  apply uniq _ (h.1.trans d.1.symm)
  simpa only [ZMod.val_natCast_of_lt (h.1 ▸ limit x), ZMod.val_natCast_of_lt (d.1 ▸ limit y)] using p0
theorem std (x : Block p j) : Holds j (least x) (index p j x) :=
  ⟨length' _, rfl⟩
theorem stdRev (x : Tower p j) : Holds j (least ((index p j).symm x)) x :=
  by simpa only [Equiv.apply_symm_apply] using std ((index p j).symm x)
omit [NeZero p] in
theorem number (h : Holds j x a) : code x = a.val := by
  have e := congrArg ZMod.val h.reads; exact (ZMod.val_natCast_of_lt (h.length ▸ limit x)).symm.trans e
end Holds

noncomputable section

def add (m n) (a : ℕ) (h : a < m+n+1) (s : Raw p × Raw p) := (merge m n ⟨a,h⟩ s).1

@[fun_prop] theorem easy_mix {X : Type*} (m n a) (h : a < m+n+1) [Codec X] {g : X→Raw p × Raw p} (e : Easy g) :
    Easy (fun x => add m n a h (g x)) := (easy_merge _ _ _ e).fstCompose

theorem merge_core (m n) (a : Fin (m+n+1)) (x y : Raw p) {j : ℕ} {v w : Tower p j}
    (h : Holds j x v) (e : Holds j y w) :
    Holds j (merge m n a (x,y)).1 ((m:ℕ)*v+(n:ℕ)*w+(a.val:ℕ)) := by
  obtain ⟨hs,hv⟩ := merged m n a x y (h.length.trans e.length.symm)
  refine ⟨hs.trans h.length,?_⟩
  suffices eq : (m:Tower p j)*↑(code x) + n*↑(code y) + ↑a.val =
      (code (merge m n a (x,y)).1: Tower p j) by rw [← h.reads, ← e.reads,eq]
  rw [h.length] at hv
  have eq := congrArg (fun x : ℕ => (x:Tower p j)) hv
  have z : ((p:Tower p j)^j)=0 := by exact_mod_cast ZMod.natCast_self (p^j)
  unfold Tower at eq
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,z,zero_mul,add_zero] using eq

variable {j : ℕ} {x y : Raw p} {v w : Tower p j}
theorem sum (m n a) (d : a < m+n+1) (h : Holds j x v) (e : Holds j y w) :
    Holds j (add m n a d (x,y)) ((m:ℕ)*v+(n:ℕ)*w+(a:ℕ)) :=
  merge_core m n ⟨a,d⟩ x y h e

theorem divided (a : Nug p) (h : Holds j x v) :
    Holds j (part a x) ((↑(a.own j)⁻¹ : Tower p j)*v) := by
  obtain ⟨r,e⟩ := h; subst j
  exact ⟨part_len ..,by rw [part_apply,e]⟩
omit [NeZero p] in
theorem turned (h : Holds j x v) :
    Holds j (veil x) (-1-v) := by
  obtain ⟨r,e⟩ := h
  refine ⟨by simp [r],?_⟩
  have eq := covered x; rw [r] at eq
  have hu := congrArg (fun x : ℕ => (x:ZMod (p^j))) eq
  simp only [Nat.cast_add,Nat.cast_one,ZMod.natCast_self,e] at hu
  apply eq_sub_of_add_eq
  apply eq_neg_of_add_eq_zero_left hu

def negative (x : Raw p) := add 1 0 1 (by decide) (veil x,x)
@[fun_prop] theorem easy_negative {X : Type*} [Codec X] {f : X→Raw p} (h : Easy f) :
    Easy (fun x => negative (f x)) := by unfold negative; fun_prop
theorem neg_correct (h : Holds j x v) : Holds j (negative x) (-v) := by
  simpa only [Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero, show -1-v+1=-v by abel,negative] using
    sum 1 0 1 (by decide) (turned h) h

def applyScale (a : Span p) (x : Raw p) :=
  let g := add a.top.count 0 0 (by omega) (x,x)
  let k := part a.down g
  bif a.neg then negative k else k

@[fun_prop] theorem easy_scale {X : Type*} (a : Span p) [Codec X] {f : X→Raw p} (h : Easy f) :
    Easy (fun i => applyScale a (f i)) := by unfold applyScale; cases a.neg <;> simp <;> fun_prop

theorem scaled (a : Span p) (h : Holds j x v) : Holds j (applyScale a x) (a.land j*v) := by
  have e0 := sum a.top.count 0 0 (by omega) h h
  simp only [Nat.cast_zero,zero_mul,add_zero] at e0
  have e := divided a.down e0
  unfold applyScale
  -- commute
  unfold Span.land Span.fold Span.polarity
  cases a.neg
  · simpa [Nug.identifies,mul_left_comm,mul_assoc] using e
  simpa [Nug.identifies,mul_left_comm,mul_assoc] using neg_correct e
end
end Adic

end IntegerMultiplication
end Computability
end OAI
