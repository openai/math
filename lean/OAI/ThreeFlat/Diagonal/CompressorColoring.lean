import OAI.Computability.VPVNP.SlotGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # Greedy coloring of the compressor's indexed base graph -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical

variable {V A : Type*} {d : ℕ} [Fintype V] [Fintype A]

/-- A greedy scan using a forbidden set at each vertex. The fresh value
enforces its unary tests and all incidences at the new vertex. Only
already-assigned vertices matter for the induction invariant. -/
theorem greedy (G : SlotGraph V d) [Nonempty A]
    (unary : V → A → Prop) (ok : V × Fin d → A → A → Prop)
    (bad : V → (V → A) → Finset A) (small : ∀ x f, (bad x f).card < Fintype.card A)
    (fresh : ∀ x f a, a ∉ bad x f → unary x a ∧
      (∀ i : Fin d, ok (x,i) a (f (G.target (x,i)).1)) ∧
      ∀ i : Fin d, ok (G.target.symm (x,i)) (f (G.target.symm (x,i)).1) a) :
    ∃ f : V → A, (∀ x, unary x (f x)) ∧ ∀ e, ok e (f e.1) (f (G.target e).1) := by
  classical
  have fill (S : Finset V) : ∃ f : V → A, (∀ x ∈ S, unary x (f x)) ∧
      ∀ e : V × Fin d, e.1 ∈ S → (G.target e).1 ∈ S → ok e (f e.1) (f (G.target e).1) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => Classical.choice inferInstance, by simp, by simp⟩
    | @insert x S hx ih =>
      obtain ⟨f,fu,fo⟩ := ih
      have exists_good : ∃ a, a ∉ bad x f := by
        by_contra! none
        have full : bad x f = Finset.univ := Finset.eq_univ_of_forall none
        simpa [full] using small x f
      obtain ⟨a,ha⟩ := exists_good
      obtain ⟨ua,fw,bw⟩ := fresh x f a ha
      refine ⟨Function.update f x a, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hS
        · simpa using ua
        · have hne : y ≠ x := fun h => hx (h ▸ hS)
          simpa [Function.update_of_ne hne] using fu y hS
      · intro e hs ht
        by_cases es : e.1 = x
        · have et : (G.target e).1 ≠ x := es ▸ G.ends_ne e
          obtain ⟨u,i⟩ := e
          change u = x at es
          subst u
          simpa [Function.update_of_ne et] using fw i
        · by_cases et : (G.target e).1 = x
          · have pair : (x,(G.target e).2) = G.target e := Prod.ext et.symm rfl
            have h := bw (G.target e).2
            rw [pair, Equiv.symm_apply_apply] at h
            simpa [Function.update_of_ne es, et] using h
          · exact (by
              simpa [Function.update_of_ne es, Function.update_of_ne et] using
                fo e ((Finset.mem_insert.mp hs).resolve_left es) ((Finset.mem_insert.mp ht).resolve_left et))
  obtain ⟨f,hu,he⟩ := fill Finset.univ
  exact ⟨f, fun x => hu x (Finset.mem_univ _), fun e => he e (Finset.mem_univ _) (Finset.mem_univ _)⟩

variable (G : SlotGraph V d)

/-- Ports in either direction, retaining parallel and oppositely directed arcs. -/
def incident (x : V) : Fin d ⊕ Fin d → V × Fin d
  | .inl i => (x,i)
  | .inr i => G.target.symm (x,i)

def adjacent (x : V) : Fin d ⊕ Fin d → V
  | .inl i => (G.target (x,i)).1
  | .inr i => (G.target.symm (x,i)).1

/-- The graph admits the paper's `2*d+1` color proper coloring. -/
theorem proper_coloring : ∃ color : V → Fin (2*d+1),
    ∀ e : V × Fin d, color e.1 ≠ color (G.target e).1 := by
  classical
  let bad (x : V) (f : V → Fin (2*d+1)) := Finset.univ.image (fun i => f (adjacent G x i))
  have small (x f) : (bad x f).card < Fintype.card (Fin (2*d+1)) := by
    have h : (bad x f).card ≤ (Finset.univ : Finset (Fin d ⊕ Fin d)).card := Finset.card_image_le
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at h ⊢
    omega
  obtain ⟨f,_,hf⟩ := greedy G (fun _ _ => True) (fun _ a b => a ≠ b) bad small (by
    intro x f a ha
    have away (i : Fin d ⊕ Fin d) : a ≠ f (adjacent G x i) := fun h =>
      ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
    exact ⟨trivial, fun i => away (.inl i), fun i => (away (.inr i)).symm⟩)
  exact ⟨f,hf⟩

end ThreeFlat.Diagonal.CompressorPacking

end OAI
