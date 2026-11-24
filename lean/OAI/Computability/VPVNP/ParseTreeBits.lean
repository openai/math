import OAI.Computability.VPVNP.ParseEventBounds
import OAI.Computability.VPVNP.ParseIncidence
import OAI.Computability.VPVNP.ParseEventValidity
import OAI.Computability.VPVNP.ParseIncidenceCNF

/-! # Parsimonious Boolean encoding of an ordered parse

The flags selected by a satisfying assignment are precisely the occurrences of
one tree. Conversely, the characteristic function of a tree's occurrences
satisfies every incidence clause. Thus summation over accepted Boolean witnesses
counts each ordered tree exactly once.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar.EventCode

variable (V H : Type*) [Fintype V] [Fintype H] (D : ℕ) (d : Fin D) (h : H)

/-- The finite Boolean word recording exactly the occurrences of the parse. -/
noncomputable def treeBits (t : OrderedParse V H d.val) :
    Fin (Fintype.card (EventCode V H D)) → Bool :=
  (selectedEquiv V H D).symm ⟨t.events 0 h, fun e he => by
    have hb := t.event_bounds 0 h he
    have hd := d.isLt
    exact e.bounded_of_wellFormed ((t.events_isParseTable 0 h).typed e he) (by omega) (by omega)⟩

@[simp] theorem selected_treeBits (t : OrderedParse V H d.val) :
    selected V H D (treeBits V H D d h t) = t.events 0 h :=
  congrArg Subtype.val ((selectedEquiv V H D).apply_symm_apply _)

theorem treeBits_satisfies (t : OrderedParse V H d.val) :
    HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) (treeBits V H D d h t) := by
  apply (satisfies_incidenceCNF_iff ..).mpr
  change IsParseTable (selected V H D (treeBits V H D d h t)) 0 d.val h
  rw [selected_treeBits]
  exact t.events_isParseTable 0 h

private theorem unique_tree
    (x : {x // HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) x}) :
    ∃! t : OrderedParse V H d.val, t.events 0 h = selected V H D x.1 :=
  ((satisfies_incidenceCNF_iff ..).mp x.2).existsUnique_parse

/-- For a fixed root degree and state, the accepting words are in bijection
with the ordered parse trees. -/
noncomputable def satisfyingEquiv :
    {x // HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) x} ≃
      OrderedParse V H d.val where
  toFun x := (unique_tree V H D d h x).exists.choose
  invFun t := ⟨treeBits V H D d h t, treeBits_satisfies V H D d h t⟩
  left_inv x := by
    apply Subtype.ext
    apply (selectedEquiv V H D).injective
    apply Subtype.ext
    rw [selectedEquiv_apply, selectedEquiv_apply, selected_treeBits]
    exact (unique_tree V H D d h x).exists.choose_spec
  right_inv t := by
    let x := (⟨treeBits V H D d h t, treeBits_satisfies V H D d h t⟩ :
      {x // HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) x})
    exact (unique_tree V H D d h x).unique (unique_tree V H D d h x).exists.choose_spec
      (selected_treeBits V H D d h t).symm

theorem events_satisfyingEquiv
    (x : {x // HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) x}) :
    (satisfyingEquiv V H D d h x).events 0 h = selected V H D x.val :=
  (unique_tree V H D d h x).exists.choose_spec

end ParseGrammar.EventCode

end VPVNP
end Computability
end OAI
