import OAI.Computability.IntegerMultiplication.Fix.Shuffle

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fix
open Code Code.Tunnel
variable {A : Type} [Codec A]
namespace Schedule
def total (l : Store A) : ℕ :=
  (l.map (fun i => size i + 1)).sum
@[simp] theorem cons (i : Key × A) (l) : total (i::l)=size i+1+total l := by simp [total]
def mass (x : Schedule A) := total x.src + total x.dest

theorem between (l : Store A) :
    total (filter false l)+total (filter true l) ≤ total l := by
  induction l with
  | nil => simp [filter,total]
  | cons i l ih =>
    obtain ⟨_|⟨h,v⟩,w⟩ := i
    · simpa only [cons,filter,select,List.flatMap_cons,List.nil_append] using
         (ih.trans (Nat.le_add_left _ _): _ ≤ size (([]:Key),w)+1+total l) -- orientation
    cases h <;>
      simp only [cons,filter,select,List.flatMap_cons,Bool.true_eq_false,Bool.false_eq_true,
        ite_true,ite_false,List.singleton_append,List.nil_append,size_prod,size_cons,show ∀ b:Bool,size b=1 from fun _ => rfl]
    all_goals unfold filter at ih; omega

theorem moves (x : Schedule A) (h : 0<x.height) :
    mass (x.child h false)+mass (x.child h true) ≤ mass x := by
  simpa [mass,child,Nat.add_add_add_comm] using
    (Nat.add_le_add (between (l:=x.src)) (between (l:=x.dest)))

theorem passenger (x y z : Schedule A) (t : branch x=some (y,z)) :
    mass y+mass z ≤ mass x ∧ 1 ≤ mass x ∧ y.height < x.height ∧ z.height<x.height := by
  unfold branch at t
  split at t
  next h =>
    by_cases v : x.src.isEmpty
    · simp [v] at t
    simp [v] at t; obtain ⟨rfl,rfl⟩ := t
    have u : 1≤total x.src := by
      cases g:x.src with
      | nil => simp [g] at v
      | cons s l => simp only [cons]; omega
    exact ⟨moves _ h,u.trans (Nat.le_add_right ..), (show x.height-1< _ by omega), by change x.height-1<x.height; omega⟩
  contradiction

theorem tallyTotal (l : Store A) :
    size l=total l+1 := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [cons,size_cons,ih]; omega
theorem sourced (l : Store A) :
    size (parcel l) ≤ size l ∧ size (blot l) ≤ size l ∧ size (road (blot l)) ≤ size l := by
  induction l with
  | nil => simp [parcel,blot,road,size_nil]
  | cons x l ih =>
    unfold blot road parcel at *
    rw [List.map_cons,List.map_cons,List.map_cons]
    simp only [size_cons,size_prod]
    change _ ∧ _ ∧ 1+_+1 ≤ _
    have v := size_pos x.1
    omega

theorem resolve :
    Sized (fun i:Schedule A => ((3*(i.height+1)*mass i + 1 : ℕ):ℝ)) input output := by
  let w (i:Schedule A) := ((mass i+1:ℕ):ℝ)
  have w0 (i:Schedule A) : 1≤w i := by simp [w]
  refine Code.Tunnel.twin branch (f:=w) (t:=side) (fun i => by exact_mod_cast Nat.le_add_left ..)
    (fun i => ?cost) height (fun a => (passenger _ _ _ a.agree).2.2) ?start ?finish
  case cost =>
    unfold w
    cases v : branch i with
    | none =>
      simp only [Option.map_none,Option.getD_none,add_zero]
      have g : mass i+1 ≤ 3*(i.height+1)*mass i+1 := by
        have := Nat.mul_le_mul_right (mass i) (show 1 ≤ 3*(i.height+1) by omega)
        omega
      exact_mod_cast g
    | some v0 =>
      obtain ⟨x,y⟩ := v0
      have ⟨n,hx0,t,u⟩ := passenger _ _ _ v
      have hi :=
        Nat.add_le_add (Nat.mul_le_mul_right (mass x)
          (Nat.mul_le_mul_left 3 (show x.height+1 ≤ i.height from t)))
          (Nat.mul_le_mul_right (mass y)
          (Nat.mul_le_mul_left 3 (show y.height+1 ≤ i.height from u)))
      have hg := Nat.mul_le_mul_left (3*i.height) n
      rw [Nat.mul_add] at hg
      have e : mass i + 1+(3*(x.height+1)*mass x+1+(3*(y.height+1)*mass y+1))
          ≤ 3*(i.height+1)*mass i+1 := by
        rw [Nat.mul_add 3 i.height,Nat.mul_one,Nat.add_mul]; omega
      simp only [Option.map_some,Option.getD_some]
      exact_mod_cast e
  case start =>
    have u (i:Schedule A) : size (question i) ≤ 3*(mass i+1) := by
      unfold question mass
      rw [size_prod,tallyTotal]
      have v := (sourced i.dest).2.1
      rw [tallyTotal] at v
      change (total i.src+1)+size (blot i.dest)+1 ≤ _
      omega
    apply Carries.cheap w0 (show Volume _ _ from ⟨3,fun i => by unfold w; exact_mod_cast u i⟩)
    exact helps
  case finish =>
    let X := Twins (branch (A:=A))
    let y (x:X) := w x.main
    let input' := fun x:X => issue branch x output side
    have v : Volume y input' := by
      refine ⟨10,fun i => ?_⟩
      have xv := (passenger _ _ _ i.agree).1
      change (((size (parcel i.x.dest)+ (size (parcel i.y.dest)+size (road (blot i.main.dest))+1)+1):ℕ):ℝ) ≤ (10:ℕ)*y i
      have Xo (s:Schedule A) : size (parcel s.dest) ≤ s.mass + 1 ∧ size (road (blot s.dest)) ≤ s.mass +1 := by
        unfold mass
        have ⟨a,b,c⟩ := sourced s.dest
        rw [tallyTotal] at *
        omega
      unfold y w
      exact_mod_cast (by
        have := Xo i.x; have := Xo i.y; have := Xo i.main
        omega : size (parcel i.x.dest)+ (size (parcel i.y.dest)+size (road (blot i.main.dest))+1)+1 ≤ 10*(i.main.mass+1))
    let m (i:X) := (parcel i.x.dest,parcel i.y.dest,road (blot i.main.dest))
    have h := Carries.func (fun i : X => w0 i.main) (show Volume y (fun i:X=>send (m i)) from v)
      (fun x : List A × List A × List Bool => joinbins (x.2.2,x.1,x.2.1)) ((by fun_prop :
        Easy (fun x : List A × List A × List Bool => (x.2.2,x.1,x.2.1))).compose easy_join_bins)
    have d (i:X) := restored i
    simp only [m,d] at h; exact h

end Schedule
end Fix

end IntegerMultiplication
end Computability
end OAI
