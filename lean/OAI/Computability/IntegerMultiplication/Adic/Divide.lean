import OAI.Computability.IntegerMultiplication.Adic.Finite

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open IntegerMultiplication.Port Code
variable {p : ℕ} [NeZero p]
noncomputable section
-- reverse call multiplication-one transfer states
private theorem quotient_hit (a : Nug p) (d : Fin p) (s : Fin a.count) :
    ∃ i : Fin a.count, ∃ u : Fin p,
      a.count*u.val+s.val = d.val+p*i.val := by
  let f := a.own 1
  have hu : IsUnit (a.count:ZMod p) :=
    (ZMod.isUnit_iff_coprime ..).mpr a.side
  let q := hu.unit
  let u : ZMod p := (↑q⁻¹ : ZMod p)*((d.val:ZMod p) - s.val)
  have e : (↑(a.count*u.val+s.val):ZMod p) = ↑d.val := by
    push_cast; rw [ZMod.natCast_zmod_val,show u= _ * _ from rfl, ← mul_assoc,
      ← hu.unit_spec, Units.mul_inv, one_mul,sub_add_cancel]
  have m := congrArg ZMod.val e
  rw [ZMod.val_natCast,ZMod.val_natCast_of_lt d.isLt] at m
  have up := u.val_lt
  have k : a.count*u.val+s.val < p*a.count := by
    have hh : a.count*(u.val+1)≤a.count*p := Nat.mul_le_mul_left _ up
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm _ p] at hh
    have z := s.isLt; omega
  let i := (a.count*u.val+s.val)/p
  have w : 0<p := Nat.pos_of_ne_zero (NeZero.ne _)
  refine ⟨⟨i,(Nat.div_lt_iff_lt_mul w).mpr (by simpa [mul_comm] using k)⟩,
    ⟨u.val,up⟩,?_⟩
  dsimp only [i]
  rw [← m, Nat.mod_add_div]

def splitter (a : Nug p) (d : Fin p) (s : Fin a.count) :
    Fin a.count × List (Fin p) :=
  ((quotient_hit a d s).choose,[(quotient_hit a d s).choose_spec.choose])

theorem hit_back (a : Nug p) (d : Fin p) (s : Fin a.count) :
    ∃ i u, splitter a d s = (i,[u]) ∧
      a.count*u.val+s.val=d.val+p*i.val :=
  ⟨_,_,rfl, (quotient_hit a d s).choose_spec.choose_spec⟩

theorem run_back (a : Nug p) (x : Raw p) (s : Fin a.count) :
    let z := machine (splitter a) (x,s)
    z.1.length=x.length ∧
    a.count*code z.1+s.val=code x+p^x.length*z.2.val := by
  induction x generalizing s with
  | nil => simp [machine_nil,code]
  | cons d x ih =>
    obtain ⟨i,u,e,d0⟩ := hit_back a d s
    obtain ⟨g,v,m⟩ : ∃ g v,machine (splitter a) (x,i)=(g,v) := ⟨_,_,rfl⟩
    specialize ih i
    rw [m] at ih
    simp [machine_cons,e,m,code,ih.1,pow_succ]
    calc
     _ = a.count*u.val+s.val+p*(a.count*code g) := by ring
     _ = d.val+p*(a.count*code g+i.val) := by rw [d0]; ring
     _ = _ := by rw [ih.2]; ring

def part (a : Nug p) (x : Raw p) : Raw p :=
  (machine (splitter a) (x,⟨0,Nat.pos_of_ne_zero a.pos⟩)).1
@[fun_prop] theorem easy_part {X : Type*} (a : Nug p) [Codec X] {v : X→Raw p} (m : Easy v) :
    Easy (fun x => part a (v x)) := by unfold part; fun_prop
@[simp] theorem part_len (a : Nug p) (v : Raw p) : (part a v).length=v.length :=
  (run_back a v _).1
theorem part_apply (a : Nug p) (v : Raw p) :
    (code (part a v) : Tower p v.length) = (↑(a.own v.length)⁻¹ : Tower p v.length)*code v := by
  -- choose k
  have h := (run_back a v (⟨0,Nat.pos_of_ne_zero a.pos⟩)).2
  simp only [Nat.add_zero] at h
  change a.count*code (part a v)=code v+p^v.length*_ at h
  let Z := Tower p v.length
  have e := congrArg (fun x : ℕ => (x:Z)) h
  unfold Z Tower at e
  push_cast at e
  have m : (p:Z)^v.length=0 := by exact_mod_cast ZMod.natCast_self (p^v.length)
  rw [m,zero_mul,add_zero, ← Nug.identifies a] at e
  rw [← e]
  rw [← mul_assoc,Units.inv_mul,one_mul]

def shade (d : Fin p) : Fin p := ⟨p-1-d.val,by have := d.isLt; omega⟩
def veil (x : Raw p) := x.map shade

omit [NeZero p] in
theorem covered (x : Raw p) :
    code (veil x)+code x+1=p^x.length := by
  induction x with
  | nil => rfl
  | cons d x ih =>
    rw [veil,List.map_cons,← show veil x = List.map shade x from rfl,code,List.length_cons,code,pow_succ',← ih]
    rw [Nat.mul_add,Nat.mul_add]
    change p-1-d.val+p*_+_+_=_
    have := d.isLt
    omega

omit [NeZero p] in
@[simp] theorem length_veil (x : Raw p) : (veil x).length=x.length := by simp [veil]
omit [NeZero p] in
@[fun_prop] theorem easy_veil {X : Type*} [Codec X] {u : X→Raw p} (e : Easy u) :
    Easy (fun x => veil (u x)) := easy_map e (Easy.finite _)
end
end Adic

end IntegerMultiplication
end Computability
end OAI
