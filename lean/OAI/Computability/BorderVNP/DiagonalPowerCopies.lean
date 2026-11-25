import OAI.Computability.BorderVNP.DiagonalPowerWords
import OAI.Computability.BorderVNP.PackedGridRepeat

/-! # Power words in repeated bottom boxes and parallel child packs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Packing Shortening MvPolynomial
open scoped Classical BigOperators

variable {D b c : ℕ} {P I : Type} [Fintype I] {bits : P → ℕ}
    {Team Param Gadget : Type*} [Fintype Team] [Fintype Param]

/-- One slice of the incident words at a repeated public grid box. Hidden
private variables can differ among the copies, so each slice has its own table. -/
def gridSlice {N : Network D P bits} {V : Type*} (i : Fin c) (table : N.Tables V) :
    (N.repeatGrid c).Tables V :=
  fun v z x => table v (fun e => Profile.blocks (z e) i)
    (fun p => x ⟨(i,p.val),p.property⟩)

/-- A public bottom site multiplies all conditioned copy terms in one box. -/
noncomputable def repeatedTags {N : Network D P bits}
    (tags : Fin c → N.Tables (Entry Param Gadget)) : (N.repeatGrid c).Tables (Entry Param Gadget) :=
  fun v z x => ∏ i, gridSlice i (tags i) v z x

omit [Fintype Param] in
/-- The interpreted grouped box contracts exactly as the product of all the
conditioned copies on independent external words. -/
theorem value_repeatedTags {N : Network D P bits} {E : Type*} [CommSemiring E]
    (tags : Fin c → N.Tables (Entry Param Gadget)) (values : Gadget → E)
    (x : Ports (fun p : Fin c × P => bits p.2)) :
    (N.repeatGrid c).value (fun v z y => interpret values (repeatedTags tags v z y)) x =
      ∏ i, N.value (fun v z y => interpret values (tags i v z y)) (fun p => x (i,p)) := by
  unfold Network.value
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (N.repeatWords c)
  intro a
  simp only [Network.read, repeatedTags, map_prod, gridSlice, Network.repeatWords]
  exact Finset.prod_comm

namespace PowerWords

/-- Keeping all copy numbers as part of the original batch labels makes
the single, repeated grid site account for each unary word precisely once. -/
noncomputable def repeated {N : Network D P bits}
    (tags : Fin c → N.Tables (Entry Param Gadget))
    (words : ∀ i, PowerWords Team Param Gadget b N (tags i)) :
    PowerWords (Fin c × Team) Param Gadget b (N.repeatGrid c) (repeatedTags tags) where
  site w := (words w.1.1).site (w.1.2, w.2)
  selected v z x w := if repeatedTags tags v z x = 0 then false else
    gridSlice w.1.1 (words w.1.1).selected v z x (w.1.2, w.2)
  located v z x w hb := by
    split at hb
    · contradiction
    · exact (words w.1.1).located v _ _ _ hb
  exact v z x := by
    by_cases hz : repeatedTags tags v z x = 0
    · simp only [hz, ite_true, slotPower_false, Finset.sum_const_zero]
      rfl
    · simp only [hz, ite_false]
      have allp := Finset.prod_ne_zero_iff.mp hz
      rw [repeatedTags, counters_prod (fun i => gridSlice i (tags i) v z x)
        (fun i => allp i (Finset.mem_univ i)), counters_passed]
      change (∑ i, (counters (tags i v _ _)).1) = _
      simp_rw [(words _).exact]
      simp only [PowerSlot, Fintype.sum_prod_type, gridSlice, slotPower]
      rfl

private theorem child_sum (i : I) (sel : PowerSlot Team Param b → Bool) :
    (∑ w, slotPower w (sel w)) =
      ∑ w : PowerSlot (I × Team) Param b, slotPower w
        (if w.1.1 = i then sel (w.1.2,w.2) else false) := by
  simp only [PowerSlot, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    rfl
  · intro j _ hji
    simp [hji]
  · simp

/-- Parallel packs use the pair of the child index and its batch as their
new batch label. All seed and initial sites retain their own local tables. -/
noncomputable def parallel {N : I → Network D P bits}
    (tags : ∀ i, (N i).Tables (Entry Param Gadget))
    (words : ∀ i, PowerWords Team Param Gadget b (N i) (tags i)) :
    PowerWords (I × Team) Param Gadget b (Network.parallel N) (Network.parallelTables N tags) where
  site w := ⟨w.1.1, (words w.1.1).site (w.1.2, w.2)⟩
  selected v z x w := if w.1.1 = v.1 then
    Network.parallelTables N (fun i => (words i).selected) v z x (w.1.2, w.2) else false
  located v z x w hb := by
    rcases v with ⟨i,v⟩
    rcases w with ⟨⟨j,t⟩,p,k⟩
    split at hb
    · rename_i hj
      change j = i at hj
      subst j
      exact congrArg (Sigma.mk i) ((words i).located v _ _ (t,p,k) hb)
    · contradiction
  exact v z x := by
    rcases v with ⟨i,v⟩
    change (counters (tags i v _ _)).1 = _
    refine ((words i).exact v _ _).trans ?_
    exact child_sum i (Network.parallelTables N (fun i => (words i).selected) ⟨i,v⟩ z x)

end PowerWords
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
