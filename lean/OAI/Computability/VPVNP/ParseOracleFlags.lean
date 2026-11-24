import OAI.Computability.VPVNP.GrammarCoefficientBounds
import OAI.Computability.VPVNP.ParseTreeBits
import OAI.Computability.VPVNP.ParseEventWeights

/-!
# A fixed flag table for the integer label coefficient oracle

In §8.1 each coefficient of `Bₓ` counts ordered parses with the requested leaves
and production multiplicities. The same incidence clauses and the same two columns
of event tags work for every word `x` and every nominated exponent vector.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open OrderedParse HardnessCNF
open scoped Classical

variable {V H α : Type*} {D m k : ℕ}

/-- One unit of multiplicity for a tag, or zero for an absent tag. -/
noncomputable def tagUnit (tag : Option α) : α →₀ ℕ :=
  tag.elim 0 (fun a ↦ Finsupp.single a 1)

/-- Count occurrences by scanning the selected coordinates of a single tag column. -/
noncomputable def tallyFlags (tags : Fin k → Option α) (flags : Fin k → Bool) : α →₀ ℕ :=
  ∑ i, if flags i then tagUnit (tags i) else 0

/-- At each coordinate the tally is the number of selected flags carrying that tag. -/
theorem tallyFlags_apply [DecidableEq α] (tags : Fin k → Option α) (flags : Fin k → Bool) (a : α) :
    tallyFlags tags flags a = (Finset.univ.filter fun i ↦ flags i = true ∧ tags i = some a).card := by
  rw [tallyFlags, Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases flags i <;> cases tags i <;> simp [tagUnit, Finsupp.single_apply]

/-- Production label of an event in the finite rectangular table. A binary event
outside the degree or split range has no label. -/
def ParseEvent.grammarLabel? (D : ℕ) (event : ParseEvent V H) : Option (GrammarLabel V H D) :=
  match event.production with
  | .inl v => some (.inl (event.state, v))
  | .inr (b, i, j) =>
    if hd : event.layer < D then
      if hb : b < event.layer then some (.inr ⟨⟨event.layer, hd⟩, event.state, ⟨b, hb⟩, i, j⟩)
      else none
    else none

/-- The fixed advice used for the flag count. The two tag columns depend only on
the candidate event. The clauses additionally fix the root layer and state. -/
structure ParseOracleMetadata (V H : Type*) (D k : ℕ) where
  /-- The fixed CNF constraints on candidate event flags used to check parse incidence. -/
  clauses : CNF k
  /-- The optional terminal-variable tag counted when the flag at this address is selected. -/
  terminal : Fin k → Option V
  /-- The optional grammar production label counted when the flag at this address is selected. -/
  label : Fin k → Option (GrammarLabel V H D)

/-- Incidence plus the two queried multiplicities. No auxiliary Boolean witnesses
are introduced by the two counts. -/
def ParseOracleMetadata.Accepts (M : ParseOracleMetadata V H D k) (input : V →₀ ℕ)
    (e : GrammarLabel V H D →₀ ℕ) (flags : Fin k → Bool) : Prop :=
  Satisfies M.clauses flags ∧ tallyFlags M.terminal flags = input ∧ tallyFlags M.label flags = e

/-- Enumerate candidate events and attach their terminal and production tags, with incidence
clauses rooted at offset zero, layer `d` and state `h`. -/
noncomputable def parseOracleMetadata (V H : Type*) [Fintype V] [Fintype H] (D : ℕ)
    (d : Fin D) (h : H) : ParseOracleMetadata V H D (Fintype.card (EventCode V H D)) where
  clauses := incidenceCNF (EventCode.enumerate V H D) 0 d.val h
  terminal i := (EventCode.enumerate V H D i).leafVariable?
  label i := (EventCode.enumerate V H D i).grammarLabel? D

private theorem sum_terminal_events {t : ℕ} (p : OrderedParse V H t) (l : ℕ) (h : H) :
    ∑ e ∈ p.events l h, tagUnit e.leafVariable? = (p.leaves.map fun v ↦ Finsupp.single v 1).sum := by
  induction p generalizing l h with
  | leaf v => simp [events, rootEvent, leaves, ParseEvent.leafVariable?, tagUnit]
  | node b i j left right ih₁ ih₂ =>
    rw [events, Finset.sum_insert (rootEvent_notMem_children b i j left right l h),
      Finset.sum_union (disjoint_childEvents b i j left right l), ih₁, ih₂]
    simp [rootEvent, leaves, ParseEvent.leafVariable?, tagUnit]

private theorem sum_label_events {t : ℕ} (p : OrderedParse V H t) (hd : t < D) (l : ℕ) (h : H) :
    ∑ e ∈ p.events l h, tagUnit (e.grammarLabel? D) = histogram ⟨t, hd⟩ h p := by
  induction p generalizing l h with
  | leaf v => simp [events, rootEvent, histogram, ParseEvent.grammarLabel?, tagUnit]
  | @node t b i j left right ih₁ ih₂ =>
    rw [events, Finset.sum_insert (rootEvent_notMem_children b i j left right l h),
      Finset.sum_union (disjoint_childEvents b i j left right l), histogram]
    rw [ih₁ (leftDegree ⟨t+1, hd⟩ b).isLt, ih₂ (rightDegree ⟨t+1, hd⟩ b).isLt]
    simp [rootEvent, ParseEvent.grammarLabel?, tagUnit, hd, b.isLt, leftDegree, rightDegree,
      add_assoc]

variable [Fintype V] [Fintype H]

private theorem tally_enumerate (tags : ParseEvent V H → Option α)
    (z : Fin (Fintype.card (EventCode V H D)) → Bool) :
    tallyFlags (fun i ↦ tags (EventCode.enumerate V H D i)) z =
      ∑ e ∈ EventCode.selected V H D z, tagUnit (tags e) := by
  rw [EventCode.selected, Finset.sum_image (EventCode.enumerate_injective V H D).injOn,
    Finset.sum_filter]
  rfl

private theorem tally_satisfying (d : Fin D) (h : H)
    (z : {z // Satisfies (incidenceCNF (EventCode.enumerate V H D) 0 d.val h) z}) :
    let p := EventCode.satisfyingEquiv V H D d h z
    let M := parseOracleMetadata V H D d h
    tallyFlags M.terminal z.val = (p.leaves.map fun v ↦ Finsupp.single v 1).sum ∧
      tallyFlags M.label z.val = histogram d h p := by
  dsimp only [parseOracleMetadata]
  rw [tally_enumerate, tally_enumerate, ← EventCode.events_satisfyingEquiv V H D d h z]
  exact ⟨sum_terminal_events _ _ _, sum_label_events _ d.isLt _ _⟩

/-- The integer coefficient equals the count of passing flag words, with one such
word for each matching ordered parse. The metadata are fixed independently of both
arguments of the oracle, `x` and `e`. -/
theorem coeff_labelQuery_eq_flagCount (d : Fin D) (h : H) (x : Fin m → Bool)
    (e : GrammarLabel (Fin m × Bool) H D →₀ ℕ) :
    (labelQuery d h x).coeff e =
      ((Finset.univ.filter ((parseOracleMetadata (Fin m × Bool) H D d h).Accepts
        (pairedExponent x) e)).card : ℤ) := by
  let V := Fin m × Bool
  let E := EventCode.satisfyingEquiv V H D d h
  let M := parseOracleMetadata V H D d h
  have hcheck (z : {z // Satisfies M.clauses z}) : M.Accepts (pairedExponent x) e z.val ↔
      ((E z).leaves : Multiset V) = (List.ofFn (fun i ↦ (i, x i)) : Multiset V) ∧
        histogram d h (E z) = e := by
    obtain ⟨ht, hl⟩ := tally_satisfying d h z
    change (Satisfies M.clauses z.val ∧ tallyFlags M.terminal z.val = pairedExponent x ∧
      tallyFlags M.label z.val = e) ↔ _
    rw [ht, hl, pairedExponent, terminalExponents_eq_query_iff]
    exact and_iff_right z.property
  rw [coeff_labelQuery_eq_card]
  congr 1
  symm
  refine Finset.card_bij
    (fun z hz ↦ E ⟨z, (Finset.mem_filter.mp hz).2.1⟩) ?_ ?_ ?_
  · intro z hz
    have ha := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcheck ⟨z, ha.1⟩).mp ha⟩
  · intro z _ w _ heq
    exact congrArg Subtype.val (E.injective heq)
  · intro p hp
    let z := E.symm p
    have hpass : M.Accepts (pairedExponent x) e z.val := by
      apply (hcheck z).mpr
      simpa [z] using (Finset.mem_filter.mp hp).2
    exact ⟨z.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpass⟩, E.apply_symm_apply p⟩

end ParseGrammar

end VPVNP
end Computability
end OAI
