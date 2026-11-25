import OAI.Hierarchy.DescentTreePrefixIntervals

namespace OAI
/-! # Choosing the chronological item of an occupied fallback-tree equality gate -/
namespace Hierarchy.DescentFallbackItemSelect
open DescentTreePrefixIntervals
open scoped Classical
noncomputable section

/-- Old local keys consist of the source, the original outgoing cable slot, and
    the grain within that cable. They are compared before the batch coordinate. -/
structure Key where
  source : ℕ
  outgoing : ℕ
  grain : ℕ
deriving DecidableEq

def Key.before (a b : Key) : Prop :=
  a.source<b.source ∨ a.source=b.source ∧
    (a.outgoing<b.outgoing ∨ a.outgoing=b.outgoing ∧ a.grain<b.grain)

theorem Key.irrefl (a : Key) : ¬a.before a := by simp [Key.before]
theorem Key.trans {a b c : Key} (ab : a.before b) (bc : b.before c) : a.before c := by
  unfold Key.before at *
  omega
theorem Key.trichotomy {a b : Key} (ne : a≠b) : a.before b ∨ b.before a := by
  rcases a with ⟨a₀,a₁,a₂⟩
  rcases b with ⟨b₀,b₁,b₂⟩
  rcases lt_trichotomy a₀ b₀ with ltSource | rfl | gtSource
  · exact Or.inl (Or.inl ltSource)
  · rcases lt_trichotomy a₁ b₁ with ltSlot | rfl | gtSlot
    · exact Or.inl (Or.inr ⟨rfl,Or.inl ltSlot⟩)
    · rcases lt_trichotomy a₂ b₂ with ltGrain | rfl | gtGrain
      · exact Or.inl (Or.inr ⟨rfl,Or.inr ⟨rfl,ltGrain⟩⟩)
      · exact (ne rfl).elim
      · exact Or.inr (Or.inr ⟨rfl,Or.inr ⟨rfl,gtGrain⟩⟩)
    · exact Or.inr (Or.inr ⟨rfl,Or.inl gtSlot⟩)
  · exact Or.inr (Or.inl gtSource)

/-- One slot per signed input, zero-filled by the physical packet builder. -/
structure Item where
  leaf : Option ℕ
  key : Key
  residual : ℕ
  signed : ℕ
  owner : Bool
  contact : ℕ

def inCell (H : ℕ) (digits : List Bool) (i : Item) : Bool :=
  match i.leaf with
  | none=>false
  | some l=>
    let d:=digits.length
    let path:=digits.get
    decide (d≤H ∧ start H path≤l ∧ l<stop H path)

def rows {K : ℕ} (H : ℕ) (path : List Bool) (items : Fin K→Item) : Finset (Fin K) :=
  Finset.univ.filter (fun j=>inCell H path (items j))

def before {K : ℕ} (items : Fin K→Item) (a b : Fin K) : Prop :=
  (items a).key.before (items b).key ∨ (items a).key=(items b).key ∧ a.val<b.val

private theorem before_trans {K : ℕ} (items : Fin K→Item) {a b c : Fin K}
    (ab : before items a b) (bc : before items b c) : before items a c := by
  rcases ab with ab | ⟨ab,t⟩ <;> rcases bc with bc | ⟨bc,v⟩
  · exact Or.inl (Key.trans ab bc)
  · exact Or.inl (bc ▸ ab)
  · exact Or.inl (ab.symm ▸ bc)
  · exact Or.inr ⟨ab.trans bc,by omega⟩

def rank {K : ℕ} (items : Fin K→Item) (live : Finset (Fin K)) (j : Fin K) :=
  (live.filter (before items · j)).card

theorem rank_lt {K : ℕ} (items : Fin K→Item) {live : Finset (Fin K)} {a b : Fin K}
    (inside : a∈live) (lt : before items a b) : rank items live a<rank items live b := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset ?_).2
  · exact ⟨a,Finset.mem_filter.mpr ⟨inside,lt⟩,by simp [before,Key.irrefl]⟩
  · intro j h
    obtain ⟨inSet,first⟩:=Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨inSet,before_trans items first lt⟩

theorem rank_inj {K : ℕ} (items : Fin K→Item) {live : Finset (Fin K)} {a b : Fin K}
    (ha : a∈live) (hb : b∈live) (eqn : rank items live a=rank items live b) : a=b := by
  by_contra ne
  have cmp : before items a b ∨ before items b a := by
    by_cases same : (items a).key=(items b).key
    · have dif : a.val≠b.val:=fun h=>ne (Fin.ext h)
      rcases lt_or_gt_of_ne dif with l|l
      · exact Or.inl (.inr ⟨same,l⟩)
      · exact Or.inr (.inr ⟨same.symm,l⟩)
    · exact (Key.trichotomy same).elim (fun l=>Or.inl (.inl l)) (fun l=>Or.inr (.inl l))
  rcases cmp with l|l
  · exact (Nat.ne_of_lt (rank_lt items ha l)) eqn
  · exact (Nat.ne_of_lt (rank_lt items hb l)) eqn.symm

def select {K : ℕ} (items : Fin K→Item) (live : Finset (Fin K)) (ordinal : ℕ) : Option (Fin K) :=
  if found : ∃j,j∈live ∧ rank items live j=ordinal then some found.choose else none

theorem select_read {K : ℕ} (items : Fin K→Item) (live : Finset (Fin K)) {j : Fin K} (hj : j∈live) :
    select items live (rank items live j)=some j := by
  have hit : ∃a,a∈live ∧ rank items live a=rank items live j:=⟨j,hj,rfl⟩
  rw [select,dite_eq_left hit,rank_inj items hit.choose_spec.1 hj hit.choose_spec.2]

theorem select_nth {K : ℕ} (items : Fin K→Item) (live : Finset (Fin K)) {j : Fin K} (hj : j∈live)
    (m : ℕ) (b : Fin m) :
    select items live ((rank items live j*m+b.val)/m)=some j := by
  have hm : 0<m:=Nat.zero_lt_of_lt b.isLt
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ hm,Nat.div_eq_of_lt b.isLt,Nat.zero_add]
  exact select_read items live hj

/-- The equality compares the two actual finite sets of earlier packets under an
    enumeration. It applies to an empty hardware cell as well. -/
theorem chronological {N K : ℕ} {X : Type*} (key : X↪Fin N) (slot : X→Fin K) (items : Fin K→Item)
    (cmp : ∀a b, (items (slot a)).key.before (items (slot b)).key ↔ key a<key b) (i j : X) :
    before items (slot i) (slot j) ↔ key i<key j := by
  constructor
  · rintro (lt | ⟨same,atLt⟩)
    · exact (cmp _ _).mp lt
    · have eqn : i=j := by
        apply key.injective
        apply le_antisymm
        · apply le_of_not_gt
          intro h
          have bad:=(cmp j i).mpr h
          rw [same] at bad
          exact Key.irrefl _ bad
        · apply le_of_not_gt
          intro h
          have bad:=(cmp i j).mpr h
          rw [same] at bad
          exact Key.irrefl _ bad
      exact False.elim ((Nat.ne_of_lt atLt) (congrArg (fun t=>(slot t).val) eqn))
  · exact fun lt=>Or.inl ((cmp _ _).mpr lt)

theorem rank_of_equiv {K L : ℕ} {X : Type*} [Fintype X] (items : Fin K→Item)
    (live : Finset (Fin K)) (coord : X≃↥live) (key : X↪Fin L)
    (order : ∀i j,before items (coord i).val (coord j).val ↔ key i<key j) (j : X) :
    rank items live (coord j).val=(Finset.univ.filter (fun i=>key i<key j)).card := by
  classical
  apply Finset.card_bij (fun i mem=>coord.symm ⟨i,(Finset.mem_filter.mp mem).1⟩)
  · intro i mem
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    apply (order _ j).mp
    simpa using (Finset.mem_filter.mp mem).2
  · intro i mi i' mi' eqn
    exact congrArg Subtype.val (coord.symm.injective eqn)
  · intro i mi
    refine ⟨(coord i).val,Finset.mem_filter.mpr ⟨(coord i).property,(order i j).mpr (Finset.mem_filter.mp mi).2⟩,?_⟩
    simp

end
end Hierarchy.DescentFallbackItemSelect

end OAI
