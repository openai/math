import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

namespace OAI
/-! # Permutation layers and cost of a good-base rotor reset -/

namespace Hierarchy.DescentRotor
open Finset
noncomputable section

/-- A bipartite multigraph of group packets is carried by at most 2L+1 permutations when
its rows and columns have at most L packets. This constant-factor edge coloring suffices
for the reset inequality and permits parallel packets with the same endpoints. -/
theorem permutation_layers {E V : Type*} [Fintype E] [DecidableEq V]
    (source target : E → V) (L : ℕ)
    (row : ∀ v, (Finset.univ.filter fun e => source e=v).card≤L)
    (col : ∀ v, (Finset.univ.filter fun e => target e=v).card≤L) :
    ∃ color : E → Fin (2*L+1), ∃ rot : Fin (2*L+1) → Equiv.Perm V,
      (∀ e, rot (color e) (source e)=target e) ∧
      ∀ e f, color e=color f → source e=source f → e=f := by
  classical
  let Proper (S : Finset E) (c : E → Fin (2*L+1)) :=
    ∀ e ∈ S, ∀ f ∈ S, c e=c f → (source e=source f ∨ target e=target f) → e=f
  have extend (S : Finset E) : ∃ c, Proper S c := by
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => 0,by simp [Proper]⟩
    | insert e S new ih =>
      obtain ⟨c,proper⟩ := ih
      let U := (Finset.univ.filter fun f => source f=source e) ∪
        (Finset.univ.filter fun f => target f=target e)
      let used := U.image c
      have count : used.card ≤ 2*L := (Finset.card_image_le).trans <|
        (Finset.card_union_le ..).trans (by have r := row (source e); have t := col (target e); omega)
      obtain ⟨fresh,hfresh⟩ : ∃ j : Fin (2*L+1), j ∉ used := by
        by_contra! full
        have all : used=Finset.univ := Finset.eq_univ_of_forall full
        rw [all,Finset.card_univ,Fintype.card_fin] at count
        omega
      have diff {f : E} (adj : source f=source e ∨ target f=target e) : c f≠fresh := by
        intro eq
        apply hfresh
        apply Finset.mem_image.mpr
        exact ⟨f,by simpa only [U,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using adj,eq⟩
      refine ⟨fun f => if f=e then fresh else c f,?_⟩
      intro x hx y hy eq adj
      by_cases xe : x=e
      · subst x
        by_contra ye
        have other : y≠e := Ne.symm ye
        simp only [ite_eq_right other] at eq
        exact diff (adj.imp Eq.symm Eq.symm) eq.symm
      by_cases ye : y=e
      · subst y
        simp only [ite_eq_right xe] at eq
        exact (diff adj eq).elim
      exact proper x ((Finset.mem_insert.mp hx).resolve_left xe) y
        ((Finset.mem_insert.mp hy).resolve_left ye) (by simpa [xe,ye] using eq) adj
  obtain ⟨c,proper⟩ := extend Finset.univ
  have source_inj (j : Fin (2*L+1)) : Function.Injective (fun e : {a : E // c a=j} => source e.val) := by
    intro e f eq
    exact Subtype.ext (proper _ (Finset.mem_univ _) _ (Finset.mem_univ _)
      (e.property.trans f.property.symm) (Or.inl eq))
  have target_inj (j : Fin (2*L+1)) : Function.Injective (fun e : {a : E // c a=j} => target e.val) := by
    intro e f eq
    exact Subtype.ext (proper _ (Finset.mem_univ _) _ (Finset.mem_univ _)
      (e.property.trans f.property.symm) (Or.inr eq))
  choose σ hσ using fun j => Equiv.Perm.exists_extending_pair _ _ (source_inj j) (target_inj j)
  refine ⟨c,σ,fun e => hσ (c e) ⟨e,rfl⟩,?_⟩
  exact fun e f eq h => proper _ (Finset.mem_univ _) _ (Finset.mem_univ _) eq (Or.inl h)

/-- Ceiling each matrix entry when packing groups of w bundles incurs at most one
partial group per destination. Every destination gets its own contiguous packet groups. -/
theorem packed_sum_le {V : Type*} [Fintype V] (bundles : V → ℕ) {w : ℕ} (hw : 0<w) :
    (∑ v, (⌈(bundles v : ℝ)/w⌉₊:ℝ)) ≤ (∑ v, (bundles v : ℝ))/w + Fintype.card V := by
  have point (v : V) : (⌈(bundles v : ℝ)/w⌉₊:ℝ) ≤ (bundles v:ℝ)/w+1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  simpa [Finset.sum_add_distrib,Finset.sum_div] using Finset.sum_le_sum (s:=Finset.univ) fun v _ => point v

/-- If every padded permutation layer costs c Y w u, the reset cost is a fixed multiple
of F B. The factor from greedy coloring is independent of Y, w, u and the integer load. -/
theorem layer_charge {c Y w u F B L : ℝ} (hc : 0≤c) (hY : 0<Y) (hw : 0<w) (hu : 0<u)
    (row : L≤10*F*B/(Y*w*u)) (one : Y*w*u≤F*B) :
    (2*L+1)*(c*Y*w*u)≤21*c*F*B := by
  have work := (le_div_iff₀ (by positivity : 0<Y*w*u)).mp row
  nlinarith only [mul_le_mul_of_nonneg_left work hc,mul_le_mul_of_nonneg_left one hc]

end
end Hierarchy.DescentRotor

end OAI
