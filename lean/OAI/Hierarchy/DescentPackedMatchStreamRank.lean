import OAI.Hierarchy.DescentPackedMatchStreamOrder
import OAI.Hierarchy.DescentOldOccurrenceRank

namespace OAI
/-! # Locate an original old occurrence by its strict three-field ordinal -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentOldOccurrenceRAM
open scoped Classical BigOperators
noncomputable section
variable {E Q : Type*} [Fintype E] {l : List Q} {key : Q→Q→Prop}

/-- A sorted finite stream with one exact position for each authentic physical pointer. -/
def streamRank (ptr : E↪Q) (member : ∀e,ptr e∈l) (onto : ∀q∈l,∃e,ptr e=q)
    (sorted : l.Pairwise key) (no : ∀a b,key a b→¬key b a) : E≃Fin l.length := by
  let j (e : E) := (List.get_of_mem (member e)).choose
  have obs (e : E) : l.get (j e)=ptr e := (List.get_of_mem (member e)).choose_spec
  have nodup : l.Nodup := sorted.imp (fun {x y} lt same=>by subst y;exact no x x lt lt)
  refine Equiv.ofBijective j ⟨fun {e f} eqn=>ptr.injective ((obs e).symm.trans ((congrArg l.get eqn).trans (obs f))),?_⟩
  intro i
  obtain ⟨e,eqn⟩ := onto (l.get i) (List.get_mem _ _)
  exact ⟨e,(List.nodup_iff_injective_get.mp nodup) ((obs e).trans eqn)⟩

omit [Fintype E] in
theorem streamRank_get (ptr : E↪Q) (member : ∀e,ptr e∈l) (onto : ∀q∈l,∃e,ptr e=q)
    (sorted : l.Pairwise key) (no : ∀a b,key a b→¬key b a) (e : E) : l.get (streamRank ptr member onto sorted no e)=ptr e :=
  (List.get_of_mem (member e)).choose_spec

theorem streamRank_count (ptr : E↪Q) (member : ∀e,ptr e∈l) (onto : ∀q∈l,∃e,ptr e=q)
    (sorted : l.Pairwise key) (no : ∀a b,key a b→¬key b a) (e : E) :
    (streamRank ptr member onto sorted no e).val=count (fun z=>key (ptr z) (ptr e)) := by
  let ix:=streamRank ptr member onto sorted no
  have before {z u : E} (lt : ix z < ix u) : key (ptr z) (ptr u) := by
    have less := List.pairwise_iff_getElem.mp sorted (ix z).val (ix u).val (ix z).isLt (ix u).isLt lt
    change key (l.get (ix z)) (l.get (ix u)) at less
    simpa only [ix,streamRank_get] using less
  have reflect (z : E) : key (ptr z) (ptr e) ↔ ix z < ix e := ⟨fun le=>by
    rcases lt_trichotomy (ix z) (ix e) with h|eqn|h
    · exact h
    · have diff:=ix.injective eqn;subst z;exact False.elim (no _ _ le le)
    · exact False.elim (no _ _ le (before h)),before⟩
  rw [count_equiv ix _ (fun j=>j < ix e) reflect]
  exact position_count (Equiv.refl (Fin l.length)) (ix e)

theorem lex_asymm {I : Type*} (a b c : I→ℕ) (x y : I) (lt : lex3 a b c x y) : ¬lex3 a b c y x := by unfold lex3 at *;omega

theorem lex_count {I : Type*} [Fintype I] (active : I→Prop) (a b c : I→ℕ) (e : I) :
    count (fun z : {i // active i}=>lex3 a b c z.val e)=
      count (fun z=>active z ∧ a z<a e)+count (fun z=>active z ∧ a z=a e ∧ b z<b e)+
      count (fun z=>active z ∧ a z=a e ∧ b z=b e ∧ c z<c e) := by
  classical
  have restrict (p : I→Prop) : count (fun z : {i // active i}=>p z.val)=count (fun z=>active z ∧ p z) := by
    unfold count
    apply Finset.card_bij (fun z _=>z.val)
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact ⟨z.property, hz⟩
    · intro _ _ _ _ same;exact Subtype.ext same
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact ⟨⟨z, hz.1⟩, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hz.2, rfl⟩
  rw [restrict (fun z => lex3 a b c z e)]
  simp only [count_eq_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases live : active j
  · rcases lt_trichotomy (a j) (a e) with ha | ha | ha
    · simp [lex3, live, ha, ha.ne]
    · rcases lt_trichotomy (b j) (b e) with hb | hb | hb
      · simp [lex3, live, ha, hb, hb.ne]
      · simp [lex3, live, ha, hb]
      · simp [lex3, live, ha, hb.ne', not_lt.mpr hb.le]
    · simp [lex3, live, ha.ne', not_lt.mpr ha.le]
  · simp [live]


end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
