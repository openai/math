import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import Mathlib.Algebra.BigOperators.Ring.Finset

section
/-! # Subdivision preserves the contraction in every characteristic -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} [Field F] {a b : Wire} (G : Diagram F a b) (x : Val a) (y : Val b)

private def inflate (s : G.E → Bool) : G.End → Bool :=
  Sum.elim (Sum.elim (bits a x) s) (Sum.elim (bits b y) s)

private theorem joint_one (s : G.E → Bool) (j : G.Joint) :
    G.normalized.vertex x y (G.inflate x y s) (.inr j) = 1 := by
  rcases j with i | j | e
  · change (if bits a x i = bits a x i then 1 else 0) = 1
    simp
  · change (if bits b y j = bits b y j then 1 else 0) = 1
    simp
  · change (if s e = s e then 1 else 0) = 1
    simp

private theorem product_inflate (s : G.E → Bool) :
    ∏ v, G.normalized.vertex x y (G.inflate x y s) v = ∏ v, G.vertex x y s v := by
  rw [Fintype.prod_sum_type]
  have hj : (∏ j : G.Joint, G.normalized.vertex x y (G.inflate x y s) (.inr j)) = 1 :=
    Finset.prod_eq_one (fun j _ => G.joint_one x y s j)
  rw [hj, mul_one]
  rfl

private theorem exists_inflate (z : G.End → Bool)
    (hz : ∏ v, G.normalized.vertex x y z v ≠ 0) :
    ∃ s, G.inflate x y s = z := by
  classical
  have ne (j : G.Joint) := Finset.prod_ne_zero_iff.mp hz (.inr j) (Finset.mem_univ _)
  refine ⟨fun e => z (.inl (.inr e)), funext ?_⟩
  rintro ((i|e)|(j|e))
  · have h := ne (.inl i)
    change (if bits a x i = z (.inl (.inl i)) then (1 : F) else 0) ≠ 0 at h
    simpa [inflate] using h
  · rfl
  · have h := ne (.inr (.inl j))
    change (if z (.inr (.inl j)) = bits b y j then (1 : F) else 0) ≠ 0 at h
    simpa [inflate, eq_comm] using h
  · have h := ne (.inr (.inr e))
    change (if z (.inr (.inr e)) = z (.inl (.inr e)) then (1 : F) else 0) ≠ 0 at h
    simpa [inflate, eq_comm] using h

/-- Any nonzero assignment agrees on both halves of every subdivided
edge, so it comes from a unique assignment of the original edges. -/
theorem eval_normalized : G.normalized.eval x y = G.eval x y := by
  classical
  unfold eval
  let _ : DecidableEq G.End := fun _ _ => Classical.propDecidable _
  let e : (G.E → Bool) ↪ (G.End → Bool) := ⟨G.inflate x y,
    fun _ _ h => funext (fun i => congrFun h (.inl (.inr i)))⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)), Finset.sum_map]
  · exact Finset.sum_congr rfl (fun s _ => G.product_inflate x y s)
  · intro z _ h
    by_contra hn
    obtain ⟨s, rfl⟩ := G.exists_inflate x y z hn
    exact h (Finset.mem_map.mpr ⟨s, Finset.mem_univ s, rfl⟩)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-! # Contracting a self-loop inside its station's table -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Finset
open scoped Classical

variable {F : Type} {a b : Wire} (G : Diagram F a b)

private abbrev Cross := {e : G.E // G.source e ≠ G.target e}
private abbrev Loop (v : G.V) := {e : G.E // G.source e = v ∧ G.target e = v}

private def loopSrc : slots a ⊕ G.Cross → G.V :=
  Sum.elim (fun i => (G.src.symm (.inl i)).1) (fun e => G.source e.val)

private def loopDst : slots b ⊕ G.Cross → G.V :=
  Sum.elim (fun i => (G.dst.symm (.inl i)).1) (fun e => G.target e.val)

private def extendPort {I : Type} (v : G.V) (z : I ⊕ G.Cross → Bool)
    (l : G.Loop v → Bool) : I ⊕ G.E → Bool
  | .inl i => z (.inl i)
  | .inr e => if h : G.source e ≠ G.target e then z (.inr ⟨e, h⟩)
    else if hv : G.source e = v ∧ G.target e = v then l ⟨e, hv⟩ else false

variable [Field F]

private def loopWeight (v : G.V) (x : slots a ⊕ G.Cross → Bool) (y : slots b ⊕ G.Cross → Bool) : F :=
  ∑ l : G.Loop v → Bool, G.weight v (G.extendPort v x l) (G.extendPort v y l)

private theorem loopWeight_local : Local G.loopSrc G.loopDst G.loopWeight := by
  intro v x y x' y' hx hy
  apply sum_congr rfl
  intro l _
  apply G.local_weight
  · rintro (i|e) hi
    · exact hx (.inl i) hi
    · by_cases h : G.source e ≠ G.target e
      · simpa only [extendPort, dite_eq_left h] using hx (.inr ⟨e, h⟩) hi
      · simp only [extendPort, dite_eq_right h]
  · rintro (i|e) hi
    · exact hy (.inl i) hi
    · by_cases h : G.source e ≠ G.target e
      · simpa only [extendPort, dite_eq_left h] using hy (.inr ⟨e, h⟩) hi
      · simp only [extendPort, dite_eq_right h]

/-- The vertex indices and exterior ports stay in place. Every self-loop
is summed inside a single table, with no scalar divisions. -/
abbrev removeLoops : Diagram F a b := ofLocal G.loopSrc G.loopDst G.loopWeight

theorem removeLoops_loopless (e : G.removeLoops.E) : G.removeLoops.source e ≠ G.removeLoops.target e := e.2

theorem arity_removeLoops (v : G.V) : G.removeLoops.arity v ≤ G.arity v := by
  let c : G.Cross ↪ G.E := ⟨Subtype.val, Subtype.val_injective⟩
  let f := ((Function.Embedding.refl (slots a)).sumMap c).sumMap
    ((Function.Embedding.refl (slots b)).sumMap c)
  have same (p : G.removeLoops.End) : G.station (f p) = G.removeLoops.station p := by
    rcases p with (p|p)|(p|p) <;> rfl
  rw [← G.degree, ← G.removeLoops.degree]
  apply Fintype.card_le_of_injective
    (fun p : {p : G.removeLoops.End // G.removeLoops.station p = v} =>
      (⟨f p.val, (same p.val).trans p.property⟩ : {p : G.End // G.station p = v}))
  intro p q hpq
  exact Subtype.ext (f.injective (congrArg Subtype.val hpq))

private def fuse (z : G.Cross → Bool) (l : ∀ v, G.Loop v → Bool) (e : G.E) : Bool :=
  if h : G.source e ≠ G.target e then z ⟨e, h⟩
  else l (G.source e) ⟨e, rfl, (not_ne_iff.mp h).symm⟩

private def split : (G.E → Bool) ≃ (G.Cross → Bool) × (∀ v, G.Loop v → Bool) where
  toFun z := (fun e => z e.val, fun _ e => z e.val)
  invFun p := G.fuse p.1 p.2
  left_inv z := by
    funext e
    by_cases h : G.source e ≠ G.target e <;> simp [fuse, h]
  right_inv p := by
    apply Prod.ext
    · funext e
      simp [fuse, e.property]
    · funext v e
      rcases e with ⟨e, h₁, h₂⟩
      have he : G.source e = G.target e := h₁.trans h₂.symm
      subst v
      simp [fuse, he]

omit [Field F] in
private theorem read_fuse {I : Type} (f : G.E → G.V) (hf : f = G.source ∨ f = G.target)
    (x : I → Bool) (z : G.Cross → Bool) (l : ∀ v, G.Loop v → Bool) (v : G.V) (e : G.E)
    (he : f e = v) :
    G.extendPort v (Sum.elim x z) (l v) (.inr e) = G.fuse z l e := by
  by_cases h : G.source e ≠ G.target e
  · simp [extendPort, fuse, h]
  · have H : G.source e = G.target e := not_ne_iff.mp h
    have h₁ : G.source e = v := by rcases hf with rfl|rfl <;> simpa [H] using he
    have hv : G.source e = v ∧ G.target e = v := ⟨h₁, H.symm.trans h₁⟩
    rw [extendPort, dite_eq_right h, dite_eq_left hv, fuse, dite_eq_right h]
    cases h₁
    rfl

set_option maxHeartbeats 1500000 in
theorem eval_removeLoops : G.removeLoops.eval = G.eval := by
  classical
  let : DecidableEq G.Cross := fun _ _ => Classical.propDecidable _
  funext x y
  rw [eval, eval]
  calc
    (∑ z : G.Cross → Bool, ∏ v, G.removeLoops.vertex x y z v) =
        ∑ z : G.Cross → Bool, ∑ l : ∀ v, G.Loop v → Bool, ∏ v,
          G.weight v (G.extendPort v (Sum.elim (bits a x) z) (l v))
            (G.extendPort v (Sum.elim (bits b y) z) (l v)) := by
      apply sum_congr rfl
      intro z _
      simp only [vertex_ofLocal _ _ _ G.loopWeight_local, loopWeight]
      exact Fintype.prod_sum _
    _ = ∑ z : G.Cross → Bool, ∑ l : ∀ v, G.Loop v → Bool, ∏ v, G.vertex x y (G.fuse z l) v := by
      apply sum_congr rfl
      intro z _
      apply sum_congr rfl
      intro l _
      apply prod_congr rfl
      intro v _
      change G.weight v _ _ = G.weight v (Sum.elim (bits a x) (G.fuse z l))
        (Sum.elim (bits b y) (G.fuse z l))
      apply G.local_weight
      · rintro (i|e) hi
        · rfl
        · exact G.read_fuse G.source (.inl rfl) _ z l v e hi
      · rintro (i|e) hi
        · rfl
        · exact G.read_fuse G.target (.inr rfl) _ z l v e hi
    _ = _ := by
      let f (p : (G.Cross → Bool) × (∀ v, G.Loop v → Bool)) :=
        ∏ v, G.vertex x y (G.fuse p.1 p.2) v
      calc
        _ = ∑ p, f p := (Fintype.sum_prod_type f).symm
        _ = _ := Fintype.sum_equiv G.split.symm _ _ (fun _ => rfl)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end
