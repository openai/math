import OAI.Computability.IntegerMultiplication.Atoll.Shift

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Cap Echo Strip
variable {d:ℕ}{s t:Bounds d}(e:s ≤ t)
abbrev march : List (Fin d) := List.finRange d
variable {A B C:Type} (a:B)
def present (u:Bool)(i:Fin d): (Vector_ t→A)→ Vector_ t→A:=
  fun x=>x ∘ column e (!u) i
-- unspecified inverses
abbrev stage (u:Bool) (i:Fin d): Equiv.Perm (Vector_ t):=
  if u then bridgeT e i else (bridgeT e i).symm -- Bool expected Prop coercion
private theorem exhibit (u:Bool)(i)(x:Vector_ t→A): present e u i x = x ∘ (stage e u i).symm := by cases u <;> rfl
def longT (u:Bool)(l: List (Fin d)):Equiv.Perm (Vector_ t) :=
  l.foldr (fun i v=> v.trans (stage e u i)) (Equiv.refl _)
private theorem vis (l) (x:Vector_ t):
    longT e true l x = l.foldr (fun j v=>column e true j v) x := by
  induction l with
  | nil=>rfl
  | cons i l ih=>
    change stage e true i _=_
    rw [show (l.foldr _ _)=longT e true l from rfl]
    rw [ih];rfl
private theorem consignG (p q):
    longT e true (p++q) = (longT e true q).trans (longT e true p) := by
  induction p with
  | nil=>ext x; rfl
  | cons i l h=>
    refine Equiv.ext fun x=>?_
    change bridgeT e i ((longT e true (l++q)) _) = _
    rw [h];rfl
theorem consign (l):
    (longT e true l).symm = longT e false l.reverse := by
  induction l using List.reverseRecOn with
  | nil=>rfl
  | append_singleton l i ih=>
    rw [consignG]
    simp_rw [List.reverse_append]
    refine Equiv.ext fun x=>?_
    change (longT e true [i]).symm ((longT e true l).symm x)= (longT e false (_ :: _) x)
    rw [ih]
    rfl
theorem inFrame (l:List (Fin d)) (x:Vector_ t→A)(u):
    l.foldr (present e u) x = x ∘ (longT e u l).symm:= by
  induction l with
  | nil=>rfl
  | cons i l ih=>
    rw [List.foldr_cons,exhibit,ih]; rfl

variable (h:Nice s)
theorem cameo (x:Vector_ s):
    longT e true march (patch e x)=patch e (turn h x) := by
  rw [vis]
  have H := imageT e h x march
    (by apply List.pairwise_iff_getElem.mpr; intro i j h g v; simp [march,v])
  funext i
  simpa [march] using H i
theorem cameoV (x:Vector_ s):
    longT e false march.reverse (patch e x)=patch e ((tune h).symm x) := by
  rw [← consign]
  apply (longT e true march).injective
  rw [Equiv.apply_symm_apply,cameo e h]
  exact congrArg (patch e) ((tune h).apply_symm_apply x).symm
include h
theorem beyond (x:Vector_ t) (v : x∉Set.range (patch e))(u:Bool):
    (if u then longT e true march else longT e false march.reverse) x ∉ Set.range (patch e) := by
  rintro ⟨a,q⟩
  apply v
  cases u
  · change patch e a=longT e false march.reverse x at q
    refine ⟨turn h a,?_⟩
    apply (longT e false march.reverse).injective
    rw [← q,cameoV e h]
    exact congrArg (patch e) ((tune h).symm_apply_apply _)
  · change patch e a=longT e true march x at q
    refine ⟨(tune h).symm a,?_⟩
    apply (longT e true march).injective
    rw [← q,cameo e h]
    exact congrArg (patch e) ((tune h).apply_symm_apply _)
theorem matinee [Zero A] (x:Vector_ s→A):
    march.foldr (present e true) (shell x) = shell (x ∘ (tune h).symm) := by
  rw [inFrame]
  funext z
  rw [consign]
  by_cases p:z∈Set.range (patch e)
  · obtain ⟨z,rfl⟩:=p
    simp only [Function.comp_apply,cameoV e h,barter]
  change shell x _ = _
  rw [barren e _ (by exact beyond e h z p false),barren e _ p]
theorem gala (x:Vector_ t→A)(a:Vector_ s):
    march.reverse.foldr (present e false) x (patch e a)= x (patch e ((tune h) a)) := by
  rw [inFrame,← consign,Equiv.symm_symm]
  simp only [Function.comp_apply,cameo e h]
  rfl

end Atoll

end IntegerMultiplication
end Computability
end OAI
