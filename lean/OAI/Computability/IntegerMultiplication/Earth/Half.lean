import OAI.Computability.IntegerMultiplication.Strip.Pastry

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Earth
open Code Strip Net Net.Walsh Dusk
private def logic (_ : Unit) (s : Fin 2) : Fin 2 × Tally :=
  if s=0 then (1,[]) else (0,[()])
def orbit (l : Tally) := machine logic (l,0)
@[fun_prop] theorem easy_orbit : Easy orbit :=
  Easy.machine (easy_id.pair (Easy.const _))

private theorem serves (l : Tally) (u : Fin 2) :
    let v := machine logic (l,u)
    2*v.1.length+v.2.val = l.length+u.val := by
  dsimp only
  induction l generalizing u with
  | nil => rw [machine_nil]; rfl
  | cons x l ih =>
    obtain ⟨a,b,e⟩ : ∃ (a:Fin 2) (b:Tally),logic x u=(a,b) := ⟨_,_,rfl⟩
    obtain ⟨w,c,q⟩ : ∃ w c,machine logic (l,a)=(w,c) := ⟨_,_,rfl⟩
    rw [machine_cons,e]
    simp [q]
   --
    have h := ih a
    rw [q] at h; dsimp only at h
    have z : 2*b.length+a.val=1+u.val := by
      fin_cases u <;> injection e with A B
      all_goals
        change _=a at A
        change _=b at B
        rw [← A,← B]
        decide -- variables?
    omega

theorem duty (l : Tally) : (orbit l).1.length=l.length/2 ∧
    (orbit l).2.val=l.length%2 := by
  have h := serves l 0
  change 2*(orbit l).1.length+(orbit l).2.val=l.length at h
  have v := (orbit l).2.isLt
  omega

abbrev tabK := Clock × Fin 2 × Tally -- phase power mod4, odd, half count
noncomputable section -- Codec Clock
def badge (l : Tally) : tabK :=
  let x := orbit l
  (Phase.time x.1,x.2,x.1)

theorem badge_easy : Easy badge := by
  exact ((easy_orbit.fstCompose.compose Phase.easy_time).pair (easy_orbit.sndCompose.pair easy_orbit.fstCompose))
theorem badge_s (l : Tally) : badge l=(((l.length/2:ℕ):Clock),⟨l.length%2,Nat.mod_lt _ (by norm_num)⟩,tally (l.length/2)) := by
  have ⟨a,b⟩ := duty l
  simp only [badge,Phase.timely,a]
  refine Prod.ext rfl (Prod.ext (Fin.ext b) ?_)
  dsimp only
  rw [← a,Code.recover_tally] -- name
def turnK' (x : (Clock×Fin 2) × Dusk.Pair) : Dusk.Pair :=
  let s := x.1.2 != 0
  let y := if s then Dusk.join_ true x.2 else x.2
  Dusk.lunarPhase (-x.1.1) y
-- select via Task.finite_select (Phase.select_ private)
private theorem finiteRule {A Y Z} [Codec A] [Codec Y] [Codec Z] [FiniteState A]
    (f : A→Y→Z) (h : ∀ a,Easy (f a)) : Easy (fun i : A×Y=> f i.1 i.2) := by
  apply Task.finite_select (W:=A×Y) Prod.fst
  intro a
  let K := {i : A × Y // i.1=a}
  have q := (h a).on (Prod.snd ∘ (Subtype.val : K → _))
  refine (q.mono (b':=fun i=> size i.val) (by rintro ⟨⟨x,y⟩,_⟩; simp; omega)).conform (by simp) (by simp) ?_
  rintro ⟨⟨x,y⟩,rfl⟩; rfl
theorem turn_easy : Easy turnK' := by
  apply finiteRule (fun i : Clock × Fin 2=> fun y => turnK' (i,y))
  intro a
  unfold turnK'
  dsimp only
  split
  · exact (join_easy _).compose (phase_easy (-a.1))
  exact phase_easy _
def lift_run (v : tabK × Dusk.Pair) :=
  Dusk.moon (v.1.2.2,turnK' ((v.1.1,v.1.2.1),v.2))
@[fun_prop] theorem lift_easy : Easy lift_run := by
  have u := turn_easy; unfold lift_run; fun_prop
variable {R : Type} [CommRing R] (c : Quarter R)
theorem squash : c.streak false * c.streak false = (-c.i)*c.half := by
  simp only [Quarter.streak,Bool.false_eq_true,ite_false]
  calc
   _ = c.half*(c.half*((1-c.i)*(1-c.i))) := by ring
   _ = c.half*(c.half*((2:R)*(-c.i))) := by
     congr 2
     linear_combination c.ii
   _ = (-c.i)*c.half := by rw [← mul_assoc c.half 2,mul_comm c.half 2,c.twice'',one_mul,mul_comm]
theorem potent (n : ℕ) : c.streak false^n =
    ((c.half^(n/2)) * (c.ph (-((n/2:ℕ):Clock)))) *(if n%2=0 then 1 else c.streak false) := by
  let h := n/2
  conv_lhs => rw [show n=2*h+n%2 by unfold h; omega,pow_add,pow_mul,pow_two,squash,mul_pow]
  have e : -(h:Clock)=(h:Clock)*(-1) := by ring
  change ((-c.i)^h*c.half^h)* _= ((c.half^h) * (c.ph (-↑h))) * _
  rw [e,← Phase.ph_pow,c.back,mul_comm ((-c.i)^h)]
  have t : n%2=0 ∨ n%2=1 := by omega
  rcases t with t|t <;> simp [t]

variable {w : ℕ}
/-- normalize transmitted C layer for variable number of simultaneous bits -/
theorem reed (l : Tally) (h : l.length/2 ≤ w+1)
    (x : Grain w) :
    lift_run (badge l,Dusk.mark x) =
      Dusk.mark ((gaunt w).streak false ^ l.length * x) := by
  rw [potent,badge_s]
  unfold lift_run turnK'
  dsimp only
  by_cases e : l.length%2=0
  · rw [ite_eq_left e,show (⟨l.length%2,_⟩:Fin 2)=0 by ext; exact e]
    simp only [bne_self_eq_false,Bool.false_eq_true,ite_false,phased]
    rw [moonlit w _ _ (by simpa using h), tally_length]
    congr 1
    ring
  have q : (⟨l.length%2,Nat.mod_lt _ (by norm_num)⟩:Fin 2) ≠ 0 := fun m=>e (congrArg Fin.val m)
  simp only [bne_iff_ne.mpr q,ite_true,show true=(!false) from rfl,shone,phased]
  rw [moonlit w _ _ (by simpa using h),tally_length,ite_eq_right e]
  congr 1
  ring

-- 2^l in residue via inverse shift
def fill_up (x : Tally × Tally) := (cutLists (x.2,()::x.1)).2
theorem fill_easy : Easy fill_up := by
  exact (easy_cut (Easy.snd.pair (show Easy (fun x:Tally × Tally=> ()::x.1) from by fun_prop))).sndCompose
theorem top (l : Tally) (x : Grain w) (h : l.length≤w+1) :
    Dusk.moon (fill_up (tally w,l),Dusk.mark x) = Dusk.mark ((2:Grain w)^l.length*x) := by
  have e : (fill_up (tally w,l)).length=w+1-l.length := by simp [fill_up,cutLists]
  rw [moonlit w _ _ (by rw [e]; omega),e]
  congr 2
  rw [way,bends _ _ (by omega),Nat.sub_sub_self h]
  -- cast real embedding
  have q : ∀ i,(⟨(2:day w)^i,0⟩ : Grain w)= (2:Grain w)^i := by
    intro i; induction i with
    | zero => simp; rfl
    | succ i ih =>
      rw [pow_succ,pow_succ,← ih]
      ext <;> simp
      all_goals first | rfl | (change 0= _ * (0:day w); simp)
  exact q _

end
end Earth

end IntegerMultiplication
end Computability
end OAI
