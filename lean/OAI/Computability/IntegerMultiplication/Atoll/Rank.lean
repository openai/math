import OAI.Computability.IntegerMultiplication.Atoll.Order
import OAI.Computability.IntegerMultiplication.Echo.Pad

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Strip Cap Echo
variable {d:ℕ} (s:Bounds d)

theorem sumFall (x y:Vector_ s)(h:Fall x y):amount s x < amount s y:= by
  induction d with
  | zero=>exact (isEmptyElim (Classical.choose h))
  | succ d ih=>
    obtain ⟨i,h,e⟩:=h
    rw [amount_next,amount_next]
    cases i using Fin.cases with
    | zero=>
      have v:bodyV x=bodyV y:=funext fun i=>e _ (Nat.succ_pos _)
      rw [v]
      exact Nat.add_lt_add_right h _
    | succ i=>
      have H := ih (body s) (bodyV x) (bodyV y) ⟨i,h,fun j p=>e j.succ (Fin.succ_lt_succ_iff.mpr p)⟩
      have t:= (x 0).isLt
      nlinarith [Nat.mul_le_mul_left (s 0) (show amount (body s) (bodyV x)+1≤ amount (body s) (bodyV y) from H)]

noncomputable def grade : Adopt (bot s) (Series.natural (space s)) where
  cast:=rank s
  route {O} f:=by
    have M : Runs ((bot s).via (rank s)) (Digit _):=
      transfer _ _ (worst _) (fun a b e=>sumFall s a b e)
    rw [← sameness _ M (clock _)]
    exact Series.tab_via _ _ f

theorem etd {A:Type} (x:Fin (space s)→A):
    (bot s).tab (x ∘ rank s) = List.ofFn x := by
  change (bot s).tab (x ∘ (grade s).cast)=_
  rw [←(grade s).route]
  change (List.finRange _).map x=_
  apply List.ext_getElem <;> simp

variable {s}
open IntegerMultiplication.Fourier
private instance {n m: Bounds d} (x:Vector_ m) : Decidable (Valid n x) :=
  inferInstanceAs (Decidable (∀ i,(x i).val < n i))
abbrev flag (s t:Bounds d)(x:Vector_ t): Bool := decide (Valid s x)
variable {t:Bounds d}(e:s≤t)
theorem building (a b : Vector_ s)(h:Fall a b) :
    Fall (patch e a) (patch e b) := by
  obtain ⟨i,v,k⟩:= h
  exact ⟨i,v,fun j p => congrArg (glue (e j)) (k j p)⟩

theorem tender (a b : Vector_ s)(h:Rise a b):
    Rise (patch e a) (patch e b) := by
  obtain ⟨i,v,k⟩:= h; exact ⟨i,v,fun j p=> congrArg (glue (e j)) (k j p)⟩
-- filtered enumeration
private theorem filter_ (u:Series (Vector_ s))(v:Series (Vector_ t)){A:Vector_ s→Vector_ s→Prop}
    {B:Vector_ t→Vector_ t→Prop}[Std.Antisymm B][Std.Irrefl B]
    (a:Runs u A)(b:Runs v B)(p:∀ x y,A x y→ B (patch e x) (patch e y)):
    v.explore.filter (flag s t)=u.explore.map (patch e) := by
  have h : List.Pairwise B (v.explore.filter (flag s t)):= b.filter _
  have f : List.Pairwise B (u.explore.map (patch e)):= List.pairwise_map.mpr (a.imp (fun t=> p _ _ t))
  apply h.eq_of_mem_iff f
  simp only [List.mem_filter,List.mem_map,flag,decide_eq_true_eq]
  rintro i
  exact ⟨fun h=>⟨Echo.recover s _ h.2,u.complete _,Echo.box e _ h.2⟩, by rintro ⟨i,-,rfl⟩; exact ⟨v.complete _,Echo.valid_ e _⟩⟩

theorem original :
    (bot t).explore.filter (flag s t)=(bot s).tab (patch e):=
  filter_ e _ _ (worst _) (worst _) (building e)
theorem stable :
    (top t).explore.filter (flag s t)=(top s).tab (patch e):=
  filter_ e _ _ (best _) (best _) (tender e)
end Atoll

end IntegerMultiplication
end Computability
end OAI
