import OAI.Computability.VPVNP.ParseEventValidity
import Mathlib.Data.Finset.Lattice.Fold

/-! # Reconstructing ordered parses from their incidence tables

Starting at a selected event, follow the two child requests to build a parse. Child
layers decrease strictly. Conversely, every selected event has a chain of parents
ending at the root. This rules out disconnected selections and makes the encoding
parsimonious.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

variable {V H : Type*}

private theorem exists_subtree {T : Finset (ParseEvent V H)}
    (htyped : ∀ e ∈ T, e.WellFormed)
    (hchildren : ∀ e ∈ T, ∀ l d h, e.Requests l d h → ∃ f ∈ T, f.Matches l d h)
    (d l : ℕ) (h : H) (hex : ∃ e ∈ T, e.Matches l d h) :
    ∃ t : OrderedParse V H d, t.events l h ⊆ T := by
  classical
  induction d using Nat.strong_induction_on generalizing l h with
  | h d ih =>
    obtain ⟨⟨l', d', h', rule⟩, he, hm⟩ := hex
    obtain ⟨rfl, rfl, rfl⟩ := hm
    have hform := htyped _ he
    rcases rule with v | ⟨b, i, j⟩
    · change d' = 0 at hform
      subst d'
      exact ⟨.leaf v, by simpa [OrderedParse.events, OrderedParse.rootEvent] using he⟩
    · change b < d' at hform
      cases d' with
      | zero => omega
      | succ k =>
        let left := hchildren _ he l' b i (Or.inl ⟨rfl, rfl, rfl⟩)
        have rlayer : k + 1 - b - 1 = k - b := by omega
        let right := hchildren _ he (l' + b + 1) (k - b) j (Or.inr ⟨rfl, rlayer.symm, rfl⟩)
        obtain ⟨t₁, ht₁⟩ := ih b hform l' i left
        obtain ⟨t₂, ht₂⟩ := ih (k - b) (by change k - b < k + 1; omega) (l' + b + 1) j right
        refine ⟨.node ⟨b, hform⟩ i j t₁ t₂, ?_⟩
        simpa [OrderedParse.events, OrderedParse.rootEvent] using
          (Finset.insert_subset_iff.mpr ⟨he, Finset.union_subset ht₁ ht₂⟩)

private theorem subtree_unique {T : Finset (ParseEvent V H)}
    (hunique : ∀ e ∈ T, ∀ f ∈ T, e.start = f.start → e.layer = f.layer → e = f)
    {d : ℕ} (t u : OrderedParse V H d) (l : ℕ) (h : H)
    (ht : t.events l h ⊆ T) (hu : u.events l h ⊆ T) : t = u := by
  classical
  induction t generalizing l h with
  | leaf v =>
    cases u with
    | leaf w =>
      have eq := hunique _ (ht (OrderedParse.rootEvent_mem _ _ _)) _
        (hu (OrderedParse.rootEvent_mem _ _ _)) rfl rfl
      have hv := congrArg ParseEvent.production eq
      simpa [OrderedParse.rootEvent] using hv
  | @node k b i j left right ih₁ ih₂ =>
    cases u with
    | node b' i' j' left' right' =>
      have eq := hunique _ (ht (OrderedParse.rootEvent_mem _ _ _)) _
        (hu (OrderedParse.rootEvent_mem _ _ _)) rfl rfl
      have hs := congrArg ParseEvent.production eq
      simp only [OrderedParse.rootEvent, Sum.inr.injEq, Prod.mk.injEq] at hs
      obtain ⟨hb, rfl, rfl⟩ := hs
      have hb' : b = b' := Fin.ext hb
      subst b'
      simp only [OrderedParse.events, Finset.insert_subset_iff, Finset.union_subset_iff] at ht hu
      rw [ih₁ left' l i ht.2.1 hu.2.1, ih₂ right' (l + b.val + 1) j ht.2.2 hu.2.2]

private theorem requested_layer_lt {e : ParseEvent V H} (hw : e.WellFormed)
    {l d : ℕ} {h : H} (hr : e.Requests l d h) : d < e.layer := by
  rcases e with ⟨l', d', h', v | ⟨b, i, j⟩⟩
  · exact hr.elim
  · change b < d' at hw
    obtain ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ := hr <;> dsimp <;> omega

/-- If two locally valid tables have the same root and one is contained in the other,
they coincide. Ascending parent links ends at the root because the table is finite. -/
private theorem eq_of_valid_subset {S T : Finset (ParseEvent V H)} {l d : ℕ} {h : H}
    (hS : IsParseTable S l d h) (hT : IsParseTable T l d h) (hst : S ⊆ T) : S = T := by
  classical
  apply Finset.Subset.antisymm hst
  intro e he
  induction e using (measure fun e : ParseEvent V H ↦ T.sup ParseEvent.layer - e.layer).wf.induction with
  | h e ih =>
    rcases hT.parent e he with hr | ⟨f, hf, hreq⟩
    · obtain ⟨g, hg, hgr⟩ := hS.root
      exact (hT.unique _ (hst hg) _ he (hgr.1.trans hr.1.symm) (hgr.2.1.trans hr.2.1.symm)) ▸ hg
    · have hlt := requested_layer_lt (hT.typed f hf) hreq
      have hmax := Finset.le_sup (f := ParseEvent.layer) hf
      have hparent : f ∈ S := ih f (by change T.sup ParseEvent.layer - f.layer < T.sup ParseEvent.layer - e.layer; omega) hf
      obtain ⟨g, hg, hgm⟩ := hS.children f hparent _ _ _ hreq
      exact (hT.unique _ (hst hg) _ he hgm.1 hgm.2.1) ▸ hg

/-- Local incidence tests give exactly one ordered parse, with one event for each
terminal or binary production occurrence. -/
theorem IsParseTable.existsUnique_parse {T : Finset (ParseEvent V H)} {l d : ℕ} {h : H}
    (hT : IsParseTable T l d h) : ∃! t : OrderedParse V H d, t.events l h = T := by
  obtain ⟨t, ht⟩ := exists_subtree hT.typed hT.children d l h hT.root
  have heq : t.events l h = T := eq_of_valid_subset (t.events_isParseTable l h) hT ht
  refine ⟨t, heq, fun u hu ↦ subtree_unique hT.unique u t l h ?_ ht⟩
  rw [hu]

end ParseGrammar

end VPVNP
end Computability
end OAI
