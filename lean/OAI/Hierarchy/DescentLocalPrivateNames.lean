import OAI.Hierarchy.DescentLivePrivateWords
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # First occurrence names for the live private words at one site -/

namespace Hierarchy.DescentLocalPrivateNames
open DescentKernelHistory DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section

variable {B Tag : Type} (r : Recipe Tag B)
abbrev Slot := Σu : r.Node, Fin (r.arity u)

def read (s : Slot r) : Option r.UsedWord :=
  match r.activePort s.1 s.2 with
  | .inl _ => none
  | .inr h => some h

theorem read_some (u : r.Node) (j : Fin (r.arity u)) (h : r.UsedWord) :
    read r ⟨u,j⟩=some h ↔ r.operand u j=.inr h.val := by
  rw [←r.activePort_read u j]
  unfold read
  cases de : r.activePort u j with
  | inl b=>simp
  | inr t=>simp [Subtype.ext_iff]

theorem hit (h : r.UsedWord) : ∃s : Slot r,read r s=some h := by
  obtain ⟨u,j,e⟩:=h.property
  exact ⟨⟨u,j⟩,(read_some r u j h).2 e⟩

variable {K a b : ℕ} (slot : Slot r ↪ Fin K)

private theorem occurs (h : r.UsedWord) : ∃n : ℕ, ∃s : Slot r,(slot s).val=n ∧ read r s=some h := by
  obtain ⟨s,hs⟩:=hit r h
  exact ⟨_,s,rfl,hs⟩

/-- The address uses the earliest genuine local operand slot, so the number
of bits is determined by the current site's operand bound at every epoch. -/
def firstAlias : r.UsedWord ↪ Fin K where
  toFun h := ⟨Nat.find (occurs r slot h),by
    obtain ⟨s,eqn,_⟩:=Nat.find_spec (occurs r slot h)
    exact eqn ▸ (slot s).isLt⟩
  inj' := by
    intro x y eqn
    obtain ⟨s,hs,readS⟩:=Nat.find_spec (occurs r slot x)
    obtain ⟨t,ht,readT⟩:=Nat.find_spec (occurs r slot y)
    have a := congrArg Fin.val eqn
    have st : s=t := slot.injective (Fin.ext (hs.trans (a.trans ht.symm)))
    exact Option.some.inj (readS.symm.trans (st ▸ readT))

theorem firstAlias_read (h : r.UsedWord) :
    ∃s,slot s=firstAlias r slot h ∧ read r s=some h := by
  obtain ⟨s,e,hs⟩:=Nat.find_spec (occurs r slot h)
  exact ⟨s,Fin.ext e,hs⟩

theorem firstAlias_le (s : Slot r) (h : r.UsedWord) (e : read r s=some h) :
    firstAlias r slot h≤ slot s :=
  Nat.find_min' _ ⟨s,rfl,e⟩

/-- The private part of the physical slot vector. A public operand and every
padding slot carry the zero digit. -/
def raw (code : r.UsedWord ↪ Cell a) (i : Fin K) : Cell a :=
  if h : ∃s,slot s=i then (read r h.choose).elim 0 code else 0

theorem raw_read (code : r.UsedWord ↪ Cell a) (s : Slot r) :
    raw r slot code (slot s)=(read r s).elim 0 code := by
  have h : ∃t,slot t=slot s:=⟨s,rfl⟩
  rw [raw,dite_eq_left h,slot.injective h.choose_spec]

theorem raw_alias (code : r.UsedWord ↪ Cell a) (nz : ∀h,code h≠0) (i : Fin K) (h : r.UsedWord) :
    raw r slot code i=code h ↔ ∃s,slot s=i ∧ read r s=some h := by
  constructor
  · intro e
    unfold raw at e
    split at e
    next occ =>
      refine ⟨occ.choose,occ.choose_spec,?_⟩
      cases hr : read r occ.choose with
      | none => simp [hr] at e;exact False.elim (nz h e.symm)
      | some v =>
        have same : v=h := code.injective (by simpa [hr] using e)
        exact congrArg some same
    next => exact False.elim (nz h e.symm)
  · rintro ⟨s,rfl,hr⟩
    simp [raw_read,hr]

/-- The shared lookup returns zero on padding/public operands, and
one plus the earliest equal slot on every private operand. -/
def renameDigit (x : Fin K → Cell a) (i : Fin K) : ℕ :=
  if x i=0 then 0 else 1+((Finset.univ.filter (fun j=>x j=x i)).min'
    ⟨i,by simp⟩).val

theorem renameDigit_actual (code : r.UsedWord ↪ Cell a) (nz : ∀h,code h≠0)
    (s : Slot r) (h : r.UsedWord) (refers : read r s=some h) :
    renameDigit (raw r slot code) (slot s)=1+(firstAlias r slot h).val := by
  let x:=raw r slot code
  have hx : x (slot s)=code h := (raw_alias r slot code nz _ _).2 ⟨s,rfl,refers⟩
  have ne : x (slot s)≠0 := hx ▸ nz h
  let hits:=Finset.univ.filter (fun j=>x j=x (slot s))
  have nonempty : hits.Nonempty:=⟨slot s,by simp [hits]⟩
  have same : hits.min' nonempty=firstAlias r slot h := by
    apply le_antisymm
    · apply Finset.min'_le
      obtain ⟨j,eqn,hr⟩:=firstAlias_read r slot h
      have v: x (firstAlias r slot h)=code h := (raw_alias r slot code nz _ _).2 ⟨j,eqn,hr⟩
      simp [hits,v,hx]
    · have mem:=Finset.min'_mem hits nonempty
      have v: x (hits.min' nonempty)=code h := (Finset.mem_filter.mp mem).2.trans hx
      obtain ⟨j,hj,hr⟩:=(raw_alias r slot code nz _ _).1 v
      exact hj ▸ firstAlias_le r slot j h hr
  change renameDigit x (slot s)=_
  rw [renameDigit,ite_eq_right ne]
  exact congrArg (fun i : Fin K=>1+i.val) same

def countCell (a K : ℕ) (v : Cell (a*K)) : ℕ :=
  ((Finset.univ.image ((encode a K).symm v)).erase 0).card

theorem countCell_actual (code : r.UsedWord ↪ Cell a) (nz : ∀h,code h≠0) :
    countCell a K (encode a K (raw r slot code))=Fintype.card r.UsedWord := by
  unfold countCell
  rw [Equiv.symm_apply_apply]
  have eqn : (Finset.univ.image (raw r slot code)).erase 0=Finset.univ.image code := by
    ext c
    simp only [Finset.mem_erase,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨ne,j,rfl⟩
      by_cases present : ∃ s, slot s = j
      · obtain ⟨s, rfl⟩ := present
        rw [raw_read] at ne ⊢
        cases hr : read r s with
        | none => simp [hr] at ne
        | some v => exact ⟨v, by simp []⟩
      · exact False.elim (ne (by simp [raw, present]))
    · rintro ⟨v,rfl⟩
      obtain ⟨s,hs⟩:=hit r v
      exact ⟨nz v,slot s,(raw_alias r slot code nz _ _).2 ⟨s,rfl,hs⟩⟩
  rw [eqn,Finset.card_image_of_injective _ code.injective,Finset.card_univ]

@[simp] theorem countCell_zero (a K : ℕ) : countCell a K 0=0 := by
  have dig : (encode a K).symm 0=fun _=>0 := by
    funext i
    apply Fin.ext
    have h:=digit_encode ((encode a K).symm 0) i
    simpa [digit] using h.symm
  unfold countCell
  rw [dig]
  apply Finset.card_eq_zero.mpr
  ext v
  simp only [Finset.mem_erase,Finset.mem_image,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
  rintro ⟨ne,j,rfl⟩
  exact ne rfl

end
end Hierarchy.DescentLocalPrivateNames

end OAI
