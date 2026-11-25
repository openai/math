import OAI.Computability.IntegerMultiplication.Fourier.Truncate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Rivulet
open IntegerMultiplication.Fourier Finset
variable {s t:ℕ}(f:Fin t→ Fin s)
abbrev plate (i:ℕ):=List.finRange i
@[simp] theorem lengthPlate (i): (plate i).length=i:=List.length_finRange
@[simp] theorem every (i:Fin s):i∈plate s:=by simp [plate]
theorem increasing : (plate s).Pairwise ((·<·):Fin s→Fin s→Prop):= by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj v
  simp [plate]; exact v

def many (i:Fin s):=List.count i (List.ofFn f)
def flow:= (plate s).flatMap (fun i=> List.replicate (many f i) i)
theorem permutes :
    (flow f).Perm (List.ofFn f) := by
  apply List.perm_iff_count.mpr
  intro a
  -- h not used? flow not unfolded!
  suffices t : ∀ (l:List (Fin s)) (v:l.Nodup), List.count a
      (l.flatMap fun i=>List.replicate (many f i) i) = if a∈ l then many f a else 0 by
    simpa [flow,many] using t (plate s) (List.nodup_finRange s)
  intro l v
  induction l with
  | nil=>simp
  | cons i l ih=>
    obtain ⟨e,g⟩:=List.nodup_cons.mp v
    by_cases u:i=a
    · subst a; simp [ih g,e]
    have d:a≠i:=Ne.symm u
    simp [List.count_replicate, u,d,ih g]

theorem patterned : (flow f).Pairwise (·≤·) := by
  rw [flow,List.pairwise_flatMap]
  constructor
  · intro a _
    apply List.pairwise_replicate.mpr
    simp
  apply increasing.imp
  intro i j h x hx y hy
  have a:=List.mem_replicate.mp hx
  have d:=List.mem_replicate.mp hy
  simp_all

  exact h.le
theorem period (a:Monotone f): flow f=List.ofFn f := by
  apply List.Perm.eq_of_pairwise _ (patterned _) _ (permutes _)
  · intro a b _ _; exact Fin.le_antisymm
  have e : (plate t).map f=List.ofFn f:=by simp [plate,List.finRange,Function.comp_def]
  rw [← e,List.pairwise_map]; exact increasing.imp (fun {_ _} t=>a t.le)
variable [NeZero t] [NeZero s] (h:s≤t)
def river (x:Fin t) : Fin s:=⟨floorSample s t x, floor_lt s t x⟩
theorem stead : Monotone (river (s:=s) (t:=t)) :=
  fun _ _ h=> Nat.div_le_div_right (Nat.mul_le_mul_left _ h)
include h
omit [NeZero t] in
theorem rise : StrictMono (pick s t h) := by
  intro i j g
  have e:2*s ≤ 2*t:= by omega
  let d:=2*s
  have p : 0<d := Nat.mul_pos (by decide) (Nat.pos_of_ne_zero (NeZero.ne _))
  let a:=2*t*i.val+s
  have t0:i.val+1≤j.val:=g
  have v:a+d≤2*t*j.val+s:= by
    unfold a d; nlinarith [Nat.mul_le_mul_left (2*t) t0]
  change a/d < (2*t*j.val+s)/d
  have W:=Nat.div_le_div_right (c:=d) v
  have b: (a+d)/d=a/d+1:=by
    rw [show a+d=a+d*1 by omega,Nat.add_mul_div_left _ _ p] -- add_mul_div_left a 1 d expects d*1
  omega

-- sets size of fibers via lists. If 3 copies => first third dist.
omit h in
theorem same (v:t≤2*s){x y:Fin t}(_z:x≤y)(e:river (s:=s) x=river y): y.val < x.val+2 := by
  by_contra! d
  let a:=s*x.val
  have u:a+t≤s*y.val:=by unfold a; nlinarith [Nat.mul_le_mul_left s d]
  have W:=Nat.div_le_div_right (c:=t) u
  have p:= Nat.pos_of_ne_zero (NeZero.ne t)
  have b : (a+t)/t=a/t+1:=by rw [show a+t=a+t*1 by omega,Nat.add_mul_div_left _ _ p]
  rw [b] at W
  have Z:= congrArg Fin.val e
  change a/t=s*y.val/t at Z
  omega

omit h in
omit [NeZero t] [NeZero s] in
private theorem eN (i:Fin s):
    many f i = ((plate t).filter (fun j=> f j == i)).length := by
  have v : List.ofFn f=(plate t).map f:= by simp [plate,List.finRange,Function.comp_def]
  unfold many; rw [List.count_eq_length_filter,v, List.filter_map] -- ?
  simp [Function.comp_def]
-- filter pairwise ordered
omit h in
omit [NeZero t] [NeZero s] in
private theorem along (i:Fin s): ((plate t).filter (fun j=> f j == i)).Pairwise ((·<·):Fin t→Fin t→Prop) := by
  apply List.Pairwise.filter _ increasing

omit h in
theorem m_f (v:t≤2*s) (i:Fin s):
    many (river (s:=s) (t:=t)) i ≤2 := by
  let f:=river (s:=s) (t:=t)
  change many f i ≤ _
  rw [eN]
  let l := ((plate t).filter (fun j=> f j== i))
  have t0:(l).Pairwise (·<·):=along f i
  have e (x:Fin t)(g:x∈l):f x=i:=by simpa [l] using g
  by_contra! u
  change _<l.length at u
  have p0 : 0<l.length:=by omega
  have p1 : 1<l.length:=by omega
  have d:=List.pairwise_iff_getElem.mp t0
  let x:=l[0]; let y:=l[1]; let z:=l[2]
  have g : x<y:=d _ _ p0 p1 (by omega)
  have m : y<z:=d _ _ p1 u (by omega)
  have V:=same (t:=t) (s:=s) v (lt_trans g m).le (show f x=f z from
    (e x (List.getElem_mem (n:=0) p0)).trans (e z (List.getElem_mem (n:=2) u)).symm)
  have q : x.val<y.val:=g; have b:y.val<z.val:=m
  omega

omit [NeZero t] in
theorem m_p(i:Fin t):
    many (pick s t h) i ≤ 1 := by
  rw [eN]
  let f:=pick s t h
  let l := ((plate s).filter (fun j=> f j== i))
  have t0:(l).Pairwise (·<·):=along f i
  have e (x:Fin s)(g:x∈l):f x=i:=by simpa [l] using g
  by_contra! b
  change _<l.length at b
  have p:0<l.length:=by omega
  let x:=l[0]; let y:=l[1]
  have g:x<y:=List.pairwise_iff_getElem.mp t0 _ _ p b (by omega)
  exact ((rise h).injective.ne (ne_of_lt g)) ((e x (List.getElem_mem (n:=0) p)).trans (e y (List.getElem_mem (n:=1) b)).symm)

-- wrap split : own offset Fin.s. arithmetic lemma use Z.
end Rivulet

end IntegerMultiplication
end Computability
end OAI
