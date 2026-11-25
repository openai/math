import OAI.Computability.IntegerMultiplication.Packed.Tags

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Code Strip Strip.Dims Loom
variable {H L i : ℕ} {I : Type} {r : Regime I}
noncomputable section
variable {H L i : I→ℕ} -- shadow
abbrev Atlas (x:I) := Plate (H x) (L x) (i x)
variable (s : r.Has fun x=> signs (H x) (L x) (i x))
variable (v : (x:I)→Atlas (H:=H) (L:=L) (i:=i) x)
variable (a : r.Has fun x=> names (v x))
include s a
theorem night : r.Has fun x => spotted (v x) := by
  suffices h : r.Has (fun x => regions (signs (H x) (L x) (i x),(names (v x)).2)) by
    simpa only [show ∀ x : I, (names (v x)).2=(badge (v x).2.1,badge (v x).2.2) from fun _=>rfl, zone] using h
  exact (s.pair (a.ez Easy.snd)).thenDo easy_regions

theorem when (t : Turn) (g : t∈order) :
    r.Has fun x => names ((walk t).symm (v x)) := by
  have f : t.shift=1 ∨ t.shift=-1 := by
    simp only [order,List.mem_cons,List.not_mem_nil,or_false] at g
    rcases g with e|e|e|e|e|e|e|e <;> subst t <;> decide
  have k : r.Has (fun x => badge (v x).1) := a.ez Easy.fst
  have b : r.Has (fun x => badge (v x).2.1) := (a.ez Easy.snd).ez Easy.fst
  have c : r.Has (fun x => badge (v x).2.2) := (a.ez Easy.snd).ez Easy.snd
  unfold walk names
  cases e : t.wing
  · simp only [Bool.false_eq_true,ite_false,Equiv.coe_fn_symm_mk]
    exact k.pair ((ripple H L i s t f (fun x => (v x).1) (fun x => (v x).2.2) k c (fun x => (v x).2.1) b).2.pair c)
  simp only [ite_true,Equiv.coe_fn_symm_mk]
  exact k.pair (b.pair (ripple H L i s t f (fun x => (v x).1) (fun x => (v x).2.1) k b (fun x => (v x).2.2) c).2)

attribute [local irreducible] order
private theorem arrive (o : List Turn) (h0 : ∀ t∈o,t∈order) :
    r.Has fun x=> emblem (names (ideal ((cruise o).symm (v x)))) := by
  have h : ∀ o : List Turn,(∀t∈o,t∈order) → r.Has fun x => names ((cruise o).symm (v x)) := by
    intro l e
    induction l with
    | nil => exact a
    | cons t l ih =>
      simp only [cruise,Equiv.symm_trans_apply]
      exact «when» s (fun x => (cruise l).symm (v x)) (ih (fun t z=>e _ (List.mem_cons_of_mem _ z))) t (e _ List.mem_cons_self)
  have x := h o h0
  let k t := (cruise o).symm (v t)
  have u : r.Has fun x=> badge (k x).1 := x.ez Easy.fst
  have y : r.Has fun x=> badge (k x).2.1 := (x.ez Easy.snd).ez Easy.fst
  have z : r.Has fun x=> badge (k x).2.2 := (x.ez Easy.snd).ez Easy.snd
  have g :
      r.Has fun x=> badge (guide (k x).1 (k x).2.1) := by
    simpa only [bright_eq] using (s.pair (u.pair y)).thenDo easy_bright
  exact (u.pair (g.pair z)).ez easy_emblem

theorem park : r.Has fun x=> emblem (names (repair (v x))) :=
  arrive s v a order (fun _ => id)

theorem send0 :
    r.Has (fun x => (spotted (v x),emblem (names (repair (v x))))) := (night s v a).pair (park s v a)
theorem send1 :
    r.Has (fun x => (spotted (v x),emblem (names (v x)))) := (night s v a).pair (a.ez easy_emblem)
end
end Packed

end IntegerMultiplication
end Computability
end OAI
