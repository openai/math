import OAI.Computability.IntegerMultiplication.Packed.Inter

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
abbrev Twirl := ℤ × ℤ
-- branch name update on right (true)
structure Turn where
  wing : Bool
  test : ℤ
  shift : ℤ
deriving DecidableEq

def compare_ (t : Turn) (c k : ℤ) := if c=1 ∧ k%2=t.test then t.shift else 0
def dance (t : Turn) (c : ℤ) (x : Twirl) : Twirl :=
  bif t.wing then (x.1,x.2+compare_ t c x.1) else (x.1+compare_ t c x.2,x.2)
def order : List Turn := [
  ⟨false,0,-1⟩,⟨true,0,-1⟩,⟨false,0,1⟩,⟨true,0,1⟩,
  ⟨true,1,1⟩,⟨false,1,1⟩,⟨true,1,-1⟩,⟨false,1,-1⟩]
abbrev ball (c : ℤ) (x : Twirl) (o : List Turn) :=
  o.foldl (fun x a => dance a c x) x
theorem all (c u v : ℤ) :
    ball c (u,v) order = (if c=1 then u+(1-2*(u%2)) else u,v) := by
  by_cases e:c=1
  · subst c
    have x : u%2=0 ∨ u%2=1 := by omega
    have y : v%2=0 ∨ v%2=1 := by omega
    rcases x with x|x <;> rcases y with y|y
    all_goals
      simp only [ball,order,List.foldl_cons,List.foldl_nil,dance,Bool.cond_false,Bool.cond_true,
        compare_,ite_true,true_and]
      -- omega explosions? rewrite ite cond %2 normalized add_mod %2. simp
      simp [Int.add_emod,x,y]
  · simp [ball,order,dance,compare_,e]
theorem safe (t : Turn) (h : t∈order) : -1≤t.shift ∧ t.shift≤1 := by
  simp only [order,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with v|v|v|v|v|v|v|v <;> subst t <;> decide

theorem moves (c k : ℤ) (t : Turn) (h : t∈order) :
    -1 ≤ compare_ t c k ∧ compare_ t c k ≤ 1 := by
  unfold compare_
  split
  · exact safe t h
  omega

-- within length bound
theorem stretch (o : List Turn) (h : ∀ t∈o,t∈order) (c : ℤ) (u w : ℤ) :
    let v := ball c (u,w) o
    (u-o.length≤v.1 ∧ v.1≤u+o.length) ∧
      (w-o.length≤v.2 ∧ v.2≤w+o.length) := by
  dsimp only
  induction o generalizing u w with
  | nil => simp [ball]
  | cons x l ih =>
    simp only [ball,List.foldl_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    obtain ⟨a,b,e⟩ : ∃ (a b : ℤ), dance x c (u,w)=(a,b) := ⟨_,_,rfl⟩
    rw [e]
    have m := ih (fun t y => h t (List.mem_cons_of_mem _ y)) a b -- ..
    have v : u-1 ≤ a ∧ a≤u+1 ∧ w-1≤b ∧ b ≤ w+1 := by
      rw [dance] at e
      cases t:x.wing <;> rw [t] at e
      all_goals
        injection e with l r
        try dsimp only at l r
        first | have h := moves c u x (h x List.mem_cons_self); omega
              | have h := moves c w x (h x List.mem_cons_self); omega
    change (u-(_+1)≤(ball c (a,b) l).1 ∧ _ ) ∧
      (w-(_+1)≤(ball c (a,b) l).2 ∧ _)
    unfold ball at *
    omega
end Packed

end IntegerMultiplication
end Computability
end OAI
