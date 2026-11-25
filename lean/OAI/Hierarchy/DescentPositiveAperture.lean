import OAI.Hierarchy.DescentWholeItems
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Forall2

namespace OAI
/-! # Ordered first fit after inserting arbitrary zero-capacity bins -/

noncomputable section
namespace Hierarchy.DescentPacking.PositiveAperture
open scoped Classical BigOperators
variable {C V I : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

def rank {T : Type*} [Fintype T] (v : T) := (Fintype.equivFin T v).val

structure Map (orig : C→ℕ) (physical : V→ℕ) where
  dest : {c // 0<orig c} ≃ {v // 0<physical v}
  mass : ∀c,physical (dest c).val=orig c.val
  order : ∀c d,rank c.val<rank d.val ↔ rank (dest c).val<rank (dest d).val

variable {orig : C→ℕ} {physical : V→ℕ}

namespace Map

def Rel (M : Map orig physical) (a : C→ℕ) (b : V→ℕ) : Prop :=
  (∀c,a c≤orig c) ∧ (∀v,b v≤physical v) ∧ ∀c,b (M.dest c).val=a c.val

def Hit (M : Map orig physical) (old : Option C) (localBin : Option V) : Prop :=
  (old=none ∧ localBin=none) ∨ ∃c,old=some c.val ∧ localBin=some (M.dest c).val

private theorem minimum {T : Type*} [Fintype T] [DecidableEq T] (cap : T→ℕ) (need : ℕ) (v w : T)
    (hit : firstFit need cap=some v) (eligible : need≤cap w) : rank v≤rank w := by
  have sorted : (binOrder T).Pairwise (fun p q=>rank p<rank q) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj ij
    simpa [binOrder,rank] using ij
  obtain ⟨_,front,tail,seq,prior⟩ := List.find?_eq_some_iff_append.mp
    (show (binOrder T).find? (fun p=>decide (need≤cap p))=some v from hit)
  have member := mem_binOrder w
  rw [seq,List.mem_append,List.mem_cons] at member
  rcases member with before|rfl|past
  · have clash := prior w before
    simp [eligible] at clash
  · rfl
  · rw [seq] at sorted
    exact ((List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 w past).le

theorem first (M : Map orig physical) (a : C→ℕ) (b : V→ℕ) (h : M.Rel a b) {need : ℕ} (pos : 0<need) :
    M.Hit (firstFit need a) (firstFit need b) := by
  cases old : firstFit need a with
  | none =>
    left
    refine ⟨rfl,?_⟩
    cases pick : firstFit need b with
    | none => rfl
    | some v =>
      have fit := firstFit_some pick
      let x : {v // 0<physical v} := ⟨v,(pos.trans_le fit).trans_le (h.2.1 v)⟩
      let c := M.dest.symm x
      have eqn : b v=a c.val := by simpa only [c,Equiv.apply_symm_apply] using h.2.2 c
      exact False.elim ((firstFit_none old c.val).not_ge (fit.trans_eq eqn))
  | some c =>
    have fit := firstFit_some old
    let u : {c // 0<orig c} := ⟨c,(pos.trans_le fit).trans_le (h.1 c)⟩
    have good : need≤b (M.dest u).val := fit.trans_eq (h.2.2 u).symm
    cases pick : firstFit need b with
    | none => exact False.elim ((firstFit_none pick _).not_ge good)
    | some v =>
      have newFit := firstFit_some pick
      let x : {v // 0<physical v} := ⟨v,(pos.trans_le newFit).trans_le (h.2.1 v)⟩
      let d := M.dest.symm x
      have eqn : b v=a d.val := by simpa only [d,Equiv.apply_symm_apply] using h.2.2 d
      have oldLe : rank u.val≤rank d.val := minimum a need c d.val old (newFit.trans_eq eqn)
      have newLe : rank (M.dest d).val≤rank (M.dest u).val := by
        simpa only [d,Equiv.apply_symm_apply] using minimum b need v (M.dest u).val pick good
      have reverse : rank d.val≤rank u.val := le_of_not_gt (fun lt=>newLe.not_gt ((M.order u d).mp lt))
      have same : u=d := Subtype.ext ((Fintype.equivFin C).injective (Fin.ext (le_antisymm oldLe reverse)))
      right
      exact ⟨u,rfl,congrArg some (show v=(M.dest u).val by rw [same];simp [d,x])⟩

private theorem consume_small {T : Type*} [DecidableEq T] (a : T→ℕ) (k : ℕ) (z : Option T) (t : T) :
    consume k a z t≤a t := by
  cases z with
  | none => rfl
  | some v =>
    by_cases same : t=v
    · subst t;simp [consume]
    · simp [consume,Function.update_of_ne,same]

private theorem consume_zero {T : Type*} [DecidableEq T] (a : T→ℕ) (z : Option T) : consume 0 a z=a := by
  cases z with
  | none => rfl
  | some v => simp [consume]

theorem step (M : Map orig physical) (a : C→ℕ) (b : V→ℕ) (h : M.Rel a b) (n : ℕ) :
    M.Rel (consume n a (firstFit n a)) (consume n b (firstFit n b)) := by
  by_cases zero : n=0
  · subst n;simpa only [consume_zero] using h
  · obtain stale|sent := M.first a b h (Nat.pos_of_ne_zero zero)
    · simpa only [stale.1,stale.2,consume] using h
    · obtain ⟨u,old,new⟩ := sent
      refine ⟨fun c=>(consume_small ..).trans (h.1 c),fun v=>(consume_small ..).trans (h.2.1 v),?_⟩
      intro d
      rw [old,new]
      by_cases same : d=u
      · subst d;simp [consume,h.2.2]
      · have diff : d.val≠u.val := fun q=>same (Subtype.ext q)
        have rem : (M.dest d).val≠(M.dest u).val := fun q=>same (M.dest.injective (Subtype.ext q))
        simp [consume,Function.update_of_ne,diff,rem,h.2.2]

def Row (M : Map orig physical) (f : I→ℕ) (a : I×Option C) (b : I×Option V) :=
  a.1=b.1 ∧ (0<f a.1→M.Hit a.2 b.2)

theorem tape (M : Map orig physical) (f : I→ℕ) (xs : List I) (a : C→ℕ) (b : V→ℕ) (h : M.Rel a b) :
    List.Forall₂ (M.Row f) (pack f xs a).decisions (pack f xs b).decisions := by
  induction xs generalizing a b with
  | nil => exact .nil
  | cons i xs ih =>
    rw [pack_decisions_cons,pack_decisions_cons]
    exact .cons ⟨rfl,fun pos=>M.first a b h pos⟩ (ih _ _ (M.step a b h _))

theorem allocated (M : Map orig physical) (f : I→ℕ) (xs : List I) :
    List.Forall₂ (M.Row f) (pack f xs orig).decisions (pack f xs physical).decisions :=
  M.tape f xs orig physical ⟨fun _=>le_rfl,fun _=>le_rfl,M.mass⟩

end Map
end Hierarchy.DescentPacking.PositiveAperture

end
end OAI
