import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.IntegerMultiplication.Curtain.Circle

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain
open Code Code.Iter
variable {L:ℕ} (p: Equiv.Perm (Fin L))
abbrev Count := Tally
abbrev Roll := List Count
abbrev paint (f : Fin L→Fin L) := List.ofFn fun i=> tally (f i).val -- parser??
def star (x : Roll×Count) := pick [] x
@[fun_prop] theorem pyS : Poly star := (facile []).poly

-- repeated lookup arbitrary input
def sig (v : Count × Roll × Count) := (fun x=> star (v.2.1,x))^[v.1.length] v.2.2
@[fun_prop] theorem polyS : Poly sig :=
  Poly.bounder star pyS 2 (by
    intro x y
    have u := search_size x ([] : List Unit) y
    simp only [size_nil] at u
    apply u.trans
    have := size_pos x; omega)
theorem walked (i : Fin L) (k:ℕ) :
    sig (tally k,paint p,tally i.val)=tally (visit p i k).val := by
  simp only [sig,tally_length,visit]
  induction k generalizing i with
  | zero=> rfl
  | succ k ih=>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
    rw [star,entry,ih]

def look (g : (Roll × Count) × Count) : Count × Count :=
  (sig (g.2,g.1),g.2)
@[fun_prop] theorem findSig : Poly look := by unfold look; fun_prop

abbrev Coat := Count × Count
-- pick minimum of visited value via suffices select. Genuine poly on arbitrary.
def shade (x : Coat×Coat) : Coat :=
  bif small (x.2.1,x.1.1) then x.2 else x.1
@[fun_prop] theorem polyShade : Poly shade := by
  have u : Poly (small (X:=Unit) (Y:=Unit)) := small_easy.poly
  unfold shade
  fun_prop

def twig (g : List Coat× Coat) := g.1.foldl (fun i a=> shade (i,a)) g.2
@[fun_prop] theorem polyTwig : Poly twig :=
  Poly.fold_left polyShade 2 1 (fun s l h=> by
    suffices e : ∀ (z:List Coat) (x:Coat),size (twig (z,x)) ≤ size z+ size x by
      have i : size l ≤ size s.1 := by
        obtain ⟨t,ht⟩ := h
        have := size_append_right l t
        have := size_pos t
        rw [← ht]; omega
      obtain ⟨v,x⟩ := s
      rw [pow_one]
      exact (e l x).trans (by dsimp at i; have z1 : size (v,x) = size v+size x+1 := rfl; omega)
    intro z
    induction z with
    | nil=> intro v; simp [twig]
    | cons a z ih=>
      intro v; change size (twig (z,shade (v,a))) ≤ size (a::z)+size v
      apply (ih _).trans
      unfold shade
      cases small (a.1,v.1) <;> simp <;> omega)
theorem branches (g : List Coat) (x : Coat) :
    let v := twig (g,x)
    (v=x ∨ v∈g) ∧ ∀ w,w∈x::g→ v.1.length≤ w.1.length := by
  induction g generalizing x with
  | nil=> simp [twig]
  | cons b g ih =>
    change let v:= twig (g,shade (x,b)); (v=x ∨ v∈b::g) ∧ ∀ w,w∈x::b::g→v.1.length≤ w.1.length
    unfold shade small
    by_cases h : b.1.length<x.1.length
    · obtain ⟨v,t⟩ := ih b
      simp only [h, decide_true, Bool.cond_true]
      refine ⟨List.mem_cons.mp ?_,?_⟩
      · apply List.mem_cons_of_mem x
        rcases v with v|v
        · rw [v]; simp
        simpa using (List.mem_cons_of_mem b v)
      intro w u
      rcases List.mem_cons.mp u with u|u
      · subst w; exact (t b (by simp)).trans h.le
      exact t w u
    obtain ⟨v,t⟩ := ih x
    simp only [h,decide_false,Bool.cond_false]
    constructor
    · exact v.imp_right (List.mem_cons_of_mem _)
    intro w u
    rcases List.mem_cons.mp u with u|u
    · subst w; exact t _ (by simp)
    rcases List.mem_cons.mp u with u|u
    · subst w; exact (t _ List.mem_cons_self).trans (le_of_not_gt h)
    exact t _ (List.mem_cons_of_mem _ u)

def scene (x : Roll × Count) : Coat :=
  twig (polyPush look (x,lineup (ruler x.1)),(x.2,[]))
@[fun_prop] theorem polyScene : Poly scene := by
  have a := Poly.push (([]:Roll),([]:Tally)) ([]:Tally) findSig
  have v : Poly (fun x : Roll × Count => lineup (ruler x.1)) :=
    (Easy.ruler Easy.fst).poly.compose poly_line
  unfold scene
  fun_prop

-- selected distance
def countK (x : Fin L) : ℕ := (scene (paint p,tally x.val)).2.length

theorem prize (x) :
    let v := scene (paint p,tally (x:Fin L).val)
    v=(tally (pole p x).val,tally (countK p x)) ∧
    visit p x (countK p x)=pole p x := by
  let t := tally x.val
  let a := lineup (ruler (paint p))
  let s := polyPush look ((paint p,t),a)
  let v := twig (s,(t,[]))
  have e : a = List.ofFn (fun i:Fin L=> tally i.val) := by
    simp [a,paint,ruler,lineup]
    funext i
    rfl
  have q : s = List.ofFn (fun i : Fin L => (tally (visit p x i.val).val,tally i.val)) := by
    unfold s polyPush
    rw [e,List.map_ofFn]
    simp [look,Function.comp_def,walked,t]
  have z : v=(t,[]) ∨ v∈s := (branches s (t,[])).1
  have m : ∀ i:Fin L,v.1.length ≤ (visit p x i).val := by
    intro i
    have e : (tally (visit p x i).val,tally i.val) ∈ (t,[])::s := by
      rw [q]; apply List.mem_cons_of_mem; simp only [List.mem_ofFn]; exact ⟨i,rfl⟩
    simpa only [tally_length] using (branches s (t,[])).2 _ e
  obtain ⟨k,ke,r⟩ := (land ..).1 (in_circle p x)
  have m₁ : v.1.length≤ (pole p x).val := by simpa only [r] using m ⟨k,ke⟩
  suffices e : ∃ b<L,v=(tally (visit p x b).val,tally b) by
    obtain ⟨b,b₁,bq⟩ := e
    have u : (pole p x).val ≤ (visit p x b).val := first_circle _ _ _ (refuge ..)
    have j : visit p x b=pole p x := by rw [bq] at m₁; simp only [tally_length] at m₁; exact Fin.ext (le_antisymm m₁ u)
    change v = _ ∧ visit p x v.2.length=_
    change v=(tally (pole p x).val,tally v.2.length) ∧ _
    simp [bq,j]
  rcases z with z|z
  · exact ⟨0,Nat.zero_lt_of_lt x.isLt,z⟩
  simp only [q,List.mem_ofFn] at z
  obtain ⟨i,t⟩ := z
  exact ⟨i,i.isLt,t.symm⟩

def frost (x : Roll × Coat) : Count :=
  sig (x.2.2,x.1,x.2.1)
def sunlight (v : Roll × Count) : Count :=
  frost (v.1,scene v)
def picture (s : Bool) (v : Roll × Count) :=
  bif s then star (v.1,sunlight v) else sunlight v
@[fun_prop] theorem polyPic (s) : Poly (picture s) := by
  unfold picture sunlight frost
  cases s <;> simp <;> fun_prop

abbrev flood (c : Bool) :=
  bif c then iron p (countK p) else ice p (countK p)
theorem prize' (x:Fin L) (s : Bool) :
    picture s (paint p,tally x.val)=tally (flood p s x).val := by
  dsimp [picture,sunlight]
  rw [(prize p x).1]
  cases s <;> simp only [frost,flood,Bool.cond_true,Bool.cond_false,walked] -- ite names
  · rfl
  rw [star,entry]; rfl

def painted (s : Bool) (v : Roll) :=
  polyPush (picture s) (v,lineup (ruler v))
@[fun_prop] theorem poly_mot (s) : Poly (painted s) := by
  unfold painted
  apply Poly.compose _ (Poly.push ([]:Roll) ([]:Count) (polyPic s))
  have a : Poly (fun v : Roll=> ruler v) := (Easy.ruler Easy.identity).poly
  fun_prop
theorem paintedR (s) :
    painted s (paint p)=paint (flood p s) := by
  unfold painted polyPush
  have q : lineup (ruler (paint p))=List.ofFn (fun i:Fin L=> tally i.val) := by
    simp [lineup,paint,ruler]
    funext i
    rfl
  rw [q,List.map_ofFn]
  simp_rw [Function.comp_def,prize']
end Curtain

end IntegerMultiplication
end Computability
end OAI
