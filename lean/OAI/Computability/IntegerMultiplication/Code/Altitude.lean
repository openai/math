import OAI.Computability.IntegerMultiplication.Code.Decompose

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Strip Adic
variable (q : ℕ) [NeZero q] (h : 2≤q)
def scaleUnit : Fin q := ⟨1,h⟩
private def more (x : Fin 3) : Raw q := if x.val=0 then [] else [scaleUnit q h]

def reload (l : Raw q) :=
  let z := Adic.merge 2 0 (⟨0,by decide⟩) (l,l)
  z.1 ++ more q h z.2
theorem reloaded : Easy (reload q h) := by
  have v := easy_merge (p:=q) 2 0 ⟨0,by decide⟩ (easy_id (X:=Raw q) |>.pair easy_id)
  have t := Easy.finite (more q h)
  exact (Easy.pair v.fstCompose (v.sndCompose.compose t)).compose Easy.append

private theorem reload_code (l : Raw q) (g : q^l.length ≤ q*code l) :
    code (reload q h l)=2*code l ∧
      q^(reload q h l).length ≤ q*code (reload q h l) := by
  obtain ⟨x,c,e⟩ : ∃ x c,merge 2 0 (⟨0,by decide⟩) (l,l)=(x,c) := ⟨_,_,rfl⟩
  have ⟨v,t⟩ := merged 2 0 ⟨0,by decide⟩ l l rfl
  simp only [e,Nat.zero_mul,Nat.add_zero] at v t
  have u : c.val ≤ 1 := by
    have hc := limit l
    by_contra z
    have hx := Nat.mul_le_mul_left (q^l.length) (by omega : 2≤c.val)
    omega
  unfold reload
  rw [e]
  dsimp only
  by_cases z : c.val=0
  · simp only [more,z,ite_true,List.append_nil,v]
    rw [z,Nat.mul_zero,Nat.add_zero] at t
    rw [← t]
    refine ⟨rfl,g.trans ?_⟩
    gcongr; omega
  have hz : c.val=1 := by omega
  simp only [more,hz,show (¬1=0) from Nat.one_ne_zero,ite_false,List.length_append,
    List.length_cons,List.length_nil,scaleUnit,cat,code,Nat.mul_zero,Nat.add_zero,Nat.mul_one,v,pow_succ]
  rw [hz,Nat.mul_one] at t
  constructor
  · exact t.symm
  rw [Nat.mul_add, Nat.mul_comm (q^l.length)]
  omega

omit [NeZero q] in
private theorem widthBound (n : ℕ) (l : Raw q) (c : ℕ) (a : ∀ i:Fin q,size i+1 ≤ c)
    (e : l.length≤n) :
    size l ≤ c*n+1 := le_trans (raw_size q c a l) (by gcongr)

def multiply (l : Raw q) (_ : Unit) := reload q h l
def altitude (l : Tally) :=
  ruler (l.foldl (multiply q h) [scaleUnit q h])

theorem grows (l : Tally) :
    2^l.length≤q^(altitude q h l).length ∧ q^(altitude q h l).length ≤ q*2^l.length ∧
    (altitude q h l).length ≤ l.length+1 := by
  have a (v:Tally) (l:Raw q) (e : q^l.length≤q*code l) :
      let z := v.foldl (multiply q h) l
      code z=code l*2^v.length ∧ q^z.length≤q*code z ∧ z.length≤v.length+l.length := by
    dsimp only
    induction v generalizing l with
    | nil => simp [e]
    | cons u v ih =>
      simp only [List.length_cons,List.foldl_cons]
      obtain ⟨g,z⟩ := reload_code q h l e
      obtain ⟨x,y,m⟩ := ih (reload q h l) z
      change _=_ ∧ _ ≤ _ ∧ (v.foldl (multiply q h) (reload q h l)).length ≤ _
      rw [show multiply q h l u=reload q h l from rfl,x,g,pow_succ]
      refine ⟨by ring,?_,?_⟩
      · rw [← g,← x]; exact y
      have hx := (merged 2 0 (⟨0,by decide⟩) l l rfl).1
      have he : (reload q h l).length ≤ l.length+1 := by
        simp only [reload,List.length_append,hx]; unfold more; split <;> simp
      omega
  have e : code [scaleUnit q h] = 1 := by simp [code,scaleUnit]
  obtain ⟨y,m,z⟩ := a l [scaleUnit q h] (by simp [e])
  rw [e,Nat.one_mul] at y
  rw [altitude,ruler_length]
  refine ⟨(by rw [← y]; exact (limit _).le),?_,z⟩
  simpa only [y] using m

theorem altitude_poly : Poly (altitude q h) := by
  have := Poly.fold_left (f:=fun x : Raw q × Unit => multiply q h x.1 x.2)
    (Easy.fst.compose (reloaded q h) |>.poly)
  obtain ⟨c,m⟩ : ∃ C : ℕ,∀ i : Fin q,size i+1 ≤ C :=
    ⟨∑ i:Fin q,(size i+1),fun i =>
      Finset.single_le_sum (f:=fun i:Fin q => size i+1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)⟩
  refine (((Easy.pair easy_id (Easy.const [scaleUnit q h])).poly.compose (this (2*c+2) 1 (fun s l e => ?_))).compose (Easy.ruler (easy_id (X:=Raw q)) |>.poly))
  apply (widthBound q (s.2.length+l.length) _ c m ?_).trans ?_
  · suffices ha : ∀ (l : Tally) (z : Raw q), (l.foldl (multiply q h) z).length ≤ z.length+l.length from ha l s.2
    intro b
    induction b with
    | nil => simp
    | cons i b ih =>
      intro a
      simp only [List.length_cons,List.foldl_cons]
      obtain x := ih (multiply q h a i)
      have y := (merged 2 0 (⟨0,by decide⟩) a a rfl).1
      change (reload q h a).length+b.length ≥ _ at x
      simp only [reload,List.length_append,y] at x
      unfold more at x
      split at x <;> simp at x <;> exact x.trans (by omega)
  have a := List.IsPrefix.length_le e
  suffices v : ∀ l:Raw q,l.length ≤ size l by
    specialize v s.2
    rw [pow_one,size_prod,size_tally]
    nlinarith [Nat.mul_le_mul_left c v,Nat.mul_le_mul_left c a]
  intro b; induction b with
  | nil => simp
  | cons u b ih => rw [List.length_cons,size_cons]; omega
end Code

end IntegerMultiplication
end Computability
end OAI
