import OAI.Hierarchy.DescentResetRetainedDecoder
import OAI.Hierarchy.DescentLocalPrivateNames

namespace OAI
/-! # The finite least-match lookup recovers the new recipe's actual first private use -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentKernelHistory DescentLocalPrivateNames
open scoped Classical Fin.CommRing
noncomputable section
variable (v : Layout)

theorem original_key (word : Cell v.siteWord) (q : Fin v.donors) (n : Fin v.previousNodes)
    (arg : Fin v.previousArgs) (present : n.val<v.originalCount word q)
    (arity : arg.val<(v.entry word q n v.arityField).val) :
    v.keyAt word (v.offset word q+n.val) arg.val=
      if (v.entry word q n (v.operandField 0 arg)).val=0 then some (q,v.entry word q n (v.operandField 2 arg)) else none :=by
  simp only [keyAt,v.location_read word q n arg present arity,Option.bind_some]

/-- Correctness rests on entries of the previous physical book only. Each
real numeric key has a unique typed word and every original use is scanned. -/
theorem first_use {Tag B : Type} (recipe : Recipe Tag B) (positions : Slot recipe↪Fin (v.nodes*v.args))
    (word : Cell v.siteWord) (x : recipe.UsedWord) (key : Fin v.donors×Cell v.bits)
    (key_iff : ∀i,v.keyIndex word i=some key ↔ ∃u : Slot recipe,positions u=i ∧ read recipe u=some x)
    (node arg : ℕ) (selected : v.keyAt word node arg=some key) :
    v.localName word node arg=(firstAlias recipe positions x).val :=by
  obtain ⟨u,atFirst,yes⟩:=firstAlias_read recipe positions x
  have hit:= (key_iff (firstAlias recipe positions x)).2 ⟨u,atFirst,yes⟩
  have found : ∃n : ℕ,∃i : Fin (v.nodes*v.args),i.val=n ∧ v.keyIndex word i=some key:=
    ⟨_,firstAlias recipe positions x,rfl,hit⟩
  simp only [localName,selected,Option.elim_some,leastSlot,dite_eq_left found]
  apply Nat.le_antisymm (Nat.find_min' found ⟨_,rfl,hit⟩)
  obtain ⟨i,idx,case_⟩:=Nat.find_spec found
  obtain ⟨k,pos,actual⟩:=(key_iff i).1 case_
  rw [←idx,←pos]
  exact firstAlias_le recipe positions k x actual

/-- Index-level matching follows from the two local decoder facts. Real
slots read their own typed keys, and unused positions of the rectangle
carry no key. This also handles a live word whose prior ordinal is zero. -/
theorem keys_match {Tag B : Type} (recipe : Recipe Tag B) (positions : Slot recipe↪Fin (v.nodes*v.args))
    (word : Cell v.siteWord) (key : recipe.UsedWord↪Fin v.donors×Cell v.bits)
    (used : ∀u,v.keyIndex word (positions u)=(read recipe u).map key)
    (empty : ∀i,(∀u,positions u≠i)→v.keyIndex word i=none) (x : recipe.UsedWord)
    (i : Fin (v.nodes*v.args)) :
    v.keyIndex word i=some (key x) ↔ ∃u,positions u=i ∧ read recipe u=some x :=by
  constructor
  · intro actual
    by_cases has : ∃u,positions u=i
    · obtain ⟨u,rfl⟩:=has
      refine ⟨u,rfl,?_⟩
      rw [used] at actual
      cases val_ : read recipe u with
      | none=>simp [val_] at actual
      | some z=>
        have eqn : key z=key x := by simpa [val_] using actual
        rw [key.injective eqn]
    · have ghost:=empty i (fun u h=>has ⟨u,h⟩)
      simp [ghost] at actual
  · rintro ⟨u,rfl,reads⟩
    simp [used,reads]

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
