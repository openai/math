import OAI.Hierarchy.DescentRotorTables
import OAI.Hierarchy.DescentRotorReset

namespace OAI
/-! # Routing the packed rows of a good base -/

namespace Hierarchy.DescentRotor

open LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits
open scoped BigOperators Classical

noncomputable section
variable {E V R : Type*}

/-- A packed group occupies one row in its layer. At every vacant site both ends
of the completed permutation receive the same prescribed dummy word. -/
def fillRows {A : Type*} (dummy : A) (slot : E → R × V) (x : E → A) (p : R × V) : A :=
  if h : ∃ e, slot e=p then x h.choose else dummy

private theorem fillRows_used {A : Type*} (dummy : A) {slot : E → R × V}
    (unique : Function.Injective slot) (x : E → A) (e : E) :
    fillRows dummy slot x (slot e)=x e := by
  have used : ∃ f, slot f=slot e := ⟨e,rfl⟩
  simp only [fillRows,dite_eq_left used]
  exact congrArg x (unique used.choose_spec)

theorem fillRows_routes {A : Type*} (dummy : A) (source target : E → V)
    (color : E → R) (rot : R → Equiv.Perm V)
    (valid : ∀ e,rot (color e) (source e)=target e)
    (unique : ∀ e f,color e=color f → source e=source f → e=f)
    (x y : E → A) :
    (∀ r v, fillRows dummy (fun e => (color e,source e)) x (r,v)=
      fillRows dummy (fun e => (color e,target e)) y (r,rot r v)) ↔ ∀e, x e=y e := by
  let src := fun e => (color e,source e)
  let dst := fun e => (color e,target e)
  have isrc : Function.Injective src := fun _ _ eq => unique _ _ (congrArg Prod.fst eq) (congrArg Prod.snd eq)
  have idst : Function.Injective dst := by
    intro e f eq
    have same := congrArg Prod.fst eq
    have ends := congrArg Prod.snd eq
    change color e=color f at same
    change target e=target f at ends
    apply unique e f same
    apply (rot (color f)).injective
    calc
      _ = target e := same ▸ valid e
      _ = target f := ends
      _ = _ := (valid f).symm
  constructor
  · intro all e
    have agree := all (color e) (source e)
    rw [valid] at agree
    change fillRows dummy src x (src e) = fillRows dummy dst y (dst e) at agree
    simpa only [fillRows_used dummy isrc,fillRows_used dummy idst] using agree
  · intro all r v
    by_cases h : ∃ e, src e=(r,v)
    · obtain ⟨e,he⟩ := h
      obtain ⟨hr,hv⟩ := Prod.mk.inj he
      subst r
      subst v
      rw [valid]
      change fillRows dummy src x (src e)=fillRows dummy dst y (dst e)
      simpa only [fillRows_used dummy isrc,fillRows_used dummy idst] using all e
    · have vacant : ¬∃e,dst e=(r,rot r v) := by
        rintro ⟨e,he⟩
        have ⟨hr,hv⟩ := Prod.mk.inj he
        apply h
        refine ⟨e,Prod.ext hr ((rot r).injective ?_)⟩
        calc
          _ = target e := hr ▸ valid e
          _ = _ := hv
      change fillRows dummy src x (r,v)=fillRows dummy dst y (r,rot r v)
      simp [fillRows,h,vacant]

/-- Contracting all configured layers agrees coefficientwise with the actual
packed-group equalities. The supply graph is common to every phase and all
choices of data; a phase only selects its fixed local table from the menu. -/
theorem good_base_layers {F : Type*} [Field F] [Fintype E] {Y : ℕ} [NeZero Y]
    {c : Fin Y → Fin Y → ℕ} {C w : ℕ}
    (menu : ∀ π : Equiv.Perm (Fin Y), Configures F c C w π)
    (source target : E → Fin Y) (L : ℕ)
    (row : ∀ v, (Finset.univ.filter fun e => source e=v).card≤L)
    (col : ∀ v, (Finset.univ.filter fun e => target e=v).card≤L) :
    ∃ color : E → Fin (2*L+1),
    ∃ tab : Fin (2*L+1) → (v : Fin Y) → Fin (2^w) → Fin (2^w) →
      (supplyGraph c).State (fun _ => Fin (2^(C*w))) v → F,
      ∀ (u : ℕ) (x y : E → Fin u → Fin (2^w)),
        (∏ r, (supplyGraph c).contraction (A:=fun _ => Fin u → Fin (2^(C*w)))
          (fun v state => ∏ k, tab r v
            (fillRows 0 (fun e => (color e,source e)) x (r,v) k)
            (fillRows 0 (fun e => (color e,target e)) y (r,v) k)
            (fun p => state p k))) =
          if ∀ e,x e=y e then 1 else 0 := by
  classical
  obtain ⟨color,rot,correct,unique⟩ := permutation_layers source target L row col
  choose tab evaluates using fun r => menu (rot r)
  refine ⟨color,tab,fun u x y => ?_⟩
  have coeff (r : Fin (2*L+1)) := evaluates r u
    (fun v => fillRows 0 (fun e => (color e,source e)) x (r,v))
    (fun v => fillRows 0 (fun e => (color e,target e)) y (r,v))
  simp_rw [coeff]
  have routed := fillRows_routes (0 : Fin u → Fin (2^w)) source target color rot correct unique x y
  by_cases equal : ∀ e, x e=y e
  · simp [routed.mpr equal,equal]
  · have fails := mt routed.mp equal
    push Not at fails
    obtain ⟨r,v,ne⟩ := fails
    rw [ite_eq_right equal]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right fun h => ne (h v))

end
end Hierarchy.DescentRotor

end OAI
