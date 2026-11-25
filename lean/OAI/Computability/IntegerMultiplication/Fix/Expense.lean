import OAI.Computability.IntegerMultiplication.Fix.Permit

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fix
open Code Strip
variable {A T : Type} [Codec A]
theorem length_key (r : Key) : size r=2*r.length+1 := by
  induction r with
  | nil => rfl
  | cons x l ih => rw [size_cons,List.length_cons,ih,show size x=1 from rfl]; omega

omit [Codec A] in
theorem length_hot (s : Series T) (m : T→Info) (x : T→A) :
    (batch true m x s).length=(s.explore.filter fun i => (m i).1).length := by
  unfold batch Ribbon.read stamps Series.tab
  induction s.explore with
  | nil => rfl
  | cons i l ih =>
    cases e : (m i).1 <;>
      simp [Ribbon.keep,e,-List.map_map,ih]

omit [Codec A] in
theorem came {s : Series T} {m : T→Info} {x:T→A} {v : Key×A} :
    v∈batch true m x s ↔ ∃ i,(m i).1=true ∧ v=((m i).2,x i) := by
  unfold batch Ribbon.read
  simp only [List.mem_flatten,List.mem_map]
  constructor
  · rintro ⟨l,⟨u,e,rfl⟩,f⟩
    rw [stamps,Series.elements] at e
    obtain ⟨i,rfl⟩ := e
    cases d : (m i).1
    · simp [Ribbon.keep,d] at f
    exact ⟨i,d,by simpa [Ribbon.keep,d] using f⟩
  rintro ⟨i,e,rfl⟩
  exact ⟨_,⟨_,(Series.elements ..).mpr ⟨i,rfl⟩,rfl⟩,by simp [Ribbon.keep,e]⟩

private theorem rate (s : Series T) (m : T→Info) (x:T→A) {d R : ℕ}
    (a : ∀ i, size (x i) ≤ R) (h : ∀i∈batch true m x s,i.1.length=d) :
    Schedule.total (batch true m x s) ≤ (2*d+R+3)*
      (s.explore.filter fun i => (m i).1).length := by
  rw [← length_hot s m x]
  let l := batch true m x s
  have t : ∀i∈l,size i+1≤2*d+R+3 := by
    intro i e
    rw [size_prod, length_key, h i e]
    obtain ⟨x,e,rfl⟩ := came.mp e
    specialize a x
    simp
    omega
  change Schedule.total l ≤ _*l.length
  generalize l=l at *
  induction l with
  | nil => simp [Schedule.total]
  | cons r l ih =>
    rw [Schedule.cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    specialize ih (fun i g => t _ (List.mem_cons_of_mem _ g))
    specialize t r List.mem_cons_self
    omega

variable {I : Type} {S T : I→Type}
variable (s : (i:I)→Series (S i)) (t : (i:I)→Series (T i))
variable (m : (i:I)→S i→Info) (z : (i:I)→T i→Info)
variable (x : (i:I)→S i→A) (y : (i:I)→T i→A)
def rarity i := ((s i).explore.filter fun a => (m i a).1).length
theorem baseline i : rarity s m i ≤ (s i).count := List.length_filter_le ..
variable {r : Regime I} {n l d : I→ℕ} {q : I→Tree}

/-- Uniform sparse work sufficient. -/
theorem allocate (g : Rule s t m z x y d)
    (a : Rip r n l q (stackRun s fun i j => send (x i j)))
    (v : Rip r n l q (stackRun s fun i j => send (m i j)))
    (v' : Rip r n l q (stackRun t fun i j => send (z i j)))
    (_sn : ∀ i,(s i).count≤n i) (_tn : ∀ i,(t i).count≤n i)
    (H : Dom r.scale d)
    (C : ℕ) (X0 : ∀ i j,size (x i j) ≤ C*(l i+1)) (Y0 : ∀ i j,size (y i j)≤C*(l i+1))
    (S0 : ∃ N : ℕ, ∀ i, (d i+1)*((rarity s m i)+(rarity t z i))≤N*n i) :
    Rip r n l q (stackRun t fun i j => send (y i j)) := by
  obtain ⟨J,u⟩ := S0
  apply g.patch s t m z x y a v v'
  obtain ⟨k,F,h⟩ := H
  obtain ⟨hi,_⟩ : (∀i,1≤n i) ∧ True := by -- from a
    obtain ⟨k,v⟩ := a
    refine ⟨fun i => ?_,trivial⟩
    by_contra e
    have h : n i=0 := by omega
    have t := v.budget i
    simp [Strip.mass,h] at t
    linarith
  refine ⟨k, (F+C+3)*6*J+1, fun i => ?_⟩
  have e := rate (s i) (m i) (x i) (X0 i) (g.snag i)
  have b := rate (t i) (z i) (y i) (Y0 i) (g.tagEnd i)
  let V := l i+(r.scale i+1)^k
  have h0 : 1 ≤ (r.scale i+1)^k := Nat.one_le_pow _ _ (by omega)
  have h1 : 2*d i + C*(l i+1)+3 ≤ 2*(F+C+3)*V := by
    specialize h i
    have c : C*(l i+1) ≤ C*V := Nat.mul_le_mul_left _ (by dsimp [V]; omega)
    have f : F*(r.scale i+1)^k ≤ F*V := Nat.mul_le_mul_left _ (by unfold V; omega)
    have h2 : 1 ≤ V := by unfold V; omega
    have hv : 0 ≤ C*V := Nat.zero_le _
    nlinarith
  suffices v : 3*(d i+1)*(Schedule.total (hot s m x i)+Schedule.total (hot t z y i))+1 ≤
      ((F+C+3)*6*J+1)*(n i*V) by
    unfold V at v
    unfold Strip.mass
    exact_mod_cast v
  calc
   _ ≤ 3*((2*d i+C*(l i+1)+3)*((d i+1)*(rarity s m i + rarity t z i)))+1 := by
    rw [Nat.mul_assoc 3]
    rw [Nat.mul_left_comm (2*d i+C*(l i+1)+3) _ _,Nat.mul_add (2*d i+C*(l i+1)+3)]
    gcongr; exacts [e,b]
   _ ≤ 3*((2*(F+C+3)*V)*(J*n i))+1 := by exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (u i))) _
   _ ≤ _ := by
    have h : 1≤n i*V := Nat.mul_pos (hi i) (by unfold V; omega)
    rw [show ((F+C+3)*6*J+1)*(n i*V)=(3*(2*(F+C+3)*V*(J*n i))+(n i*V)) by ring]
    omega
end Fix

end IntegerMultiplication
end Computability
end OAI
