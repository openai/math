import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsEncoding

/-! # Uniform type and edge tables for port-walk certificates

At each vertex a test reads its complete claimed view. Every occupied slot
compares its suffix with the truncated view at its opposite endpoint.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph
open PlanarCertSize
open RootedMap (paddedDirection)

namespace MapLabels

variable {N : ℕ}

def vertexVal (b : BaseAlphabet N) (f : VertexField) : ℕ := (b.2.2 (.inl f)).val
def portVal (b : BaseAlphabet N) (i : Fin 4) (f : PortField) : ℕ := (b.2.2 (.inr (i,f))).val

end MapLabels

namespace PortView

def center {A : Type*} : (r : ℕ) → PortView A r → A
  | 0, z => z
  | _+1, z => z.1

def shorten {A : Type*} : {r s : ℕ} → (s ≤ r) → PortView A r → PortView A s
  | 0, 0, _, z => z
  | r+1, s, h, z => if h' : s ≤ r then shorten h' (truncate r z)
      else cast (congrArg (PortView A) (by omega : r+1 = s)) z

variable {A : Type*}
variable {V E : Type*} {G : PortGraph V E} (num : G.FourPortNumbering) (b : V → A)

theorem center_actual (r : ℕ) (v : V) : center r (actual num b r v) = b v := by
  cases r <;> rfl

theorem shorten_actual {r s : ℕ} (h : s ≤ r) (v : V) :
    shorten h (actual num b r v) = actual num b s v := by
  induction r generalizing s with
  | zero =>
    obtain rfl : s = 0 := by omega
    rfl
  | succ r ih =>
    unfold shorten
    split
    · rename_i hs
      have trunc : ∀ (n : ℕ) (x : V), truncate n (actual num b (n+1) x) = actual num b n x := by
        intro n
        induction n with
        | zero => exact fun _ => rfl
        | succ n ih' =>
          intro x
          apply Prod.ext
          · rfl
          funext i
          simp only [actual, truncate, Option.map_map]
          cases G.portStep num x i with
          | none => rfl
          | some w => exact congrArg (fun t => some (w.2,t)) (ih' w.1)
      rw [trunc, ih hs]
    · obtain rfl : s = r + 1 := by omega
      rfl

end PortView

/-- A local verifier is one vertex predicate and one predicate per ordered
pair of port positions, independent of the underlying map. -/
structure MapLabelTests (A : Type*) where
  vertex : MapType → A → Prop
  edge : Fin 4 → Fin 4 → A → A → Prop

namespace MapLabelTests

variable {V E A : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable (T : MapLabelTests A) (M : RootedMap V E)

/-- Evaluate the same two tables on a presentation of a rooted map. -/
def Pass (z : V → A) : Prop :=
  (∀ v, T.vertex (M.typeAt v) (z v)) ∧
    ∀ e, T.edge (M.slots _ ⟨(e,false),rfl⟩) (M.slots _ ⟨(e,true),rfl⟩)
      (z (M.graph.tail e)) (z (M.graph.head e))

/-- Adjoin the exact local consistency checks for a view of positive radius. -/
def views {N : ℕ} (r : ℕ) (valid : PortView (BaseAlphabet N) (r+1) → Prop) :
    MapLabelTests (PortView (BaseAlphabet N) (r+1)) where
  vertex θ z := valid z ∧ z.1.1 = θ.root ∧ z.1.2.1 = paddedDirection θ ∧
    ∀ i : Fin 4, θ.degree.val ≤ i.val → z.2 i = none
  edge i j z w := z.2 i = some (j, PortView.truncate r w) ∧
    w.2 j = some (i, PortView.truncate r z)

private theorem slot_exists (v : V) (i : Fin 4) :
    (∃ p, M.slots v p = i) ↔ i.val < (M.typeAt v).degree.val := by
  constructor
  · rintro ⟨p,rfl⟩
    exact (M.num v p).isLt
  · intro h
    refine ⟨(M.num v).symm ⟨i.val,h⟩, Fin.ext ?_⟩
    change ((M.num v) ((M.num v).symm _) : ℕ) = _
    simp

/-- Passing the two finite tables forces every label to be the true walk view
of its own base fields. Conversely genuine views pass exactly when their types
and local predicates do. -/
theorem pass_views_iff {N : ℕ} (r : ℕ) (valid : PortView (BaseAlphabet N) (r+1) → Prop)
    (z : V → PortView (BaseAlphabet N) (r+1)) :
    (views r valid).Pass M z ↔
      z = PortView.actual M.slots (fun v => (z v).1) (r+1) ∧
      ∀ v, valid (z v) ∧ (z v).1.1 = (M.typeAt v).root ∧
        (z v).1.2.1 = paddedDirection (M.typeAt v) := by
  let b := fun v => (z v).1
  have loc := PortView.localTests_iff_vertex_edge M.slots b (r+1) z
  rw [← PortView.localTests_iff, loc]
  constructor
  · rintro ⟨hv,he⟩
    exact ⟨⟨fun v => ⟨rfl,fun i hi => (hv v).2.2.2 i
      (Nat.le_of_not_gt (fun h => hi ((slot_exists M v i).mpr h)))⟩, he⟩,
      fun v => ⟨(hv v).1,(hv v).2.1,(hv v).2.2.1⟩⟩
  · rintro ⟨⟨hv,he⟩,ht⟩
    refine ⟨fun v => ⟨(ht v).1,(ht v).2.1,(ht v).2.2,fun i hi => ?_⟩,he⟩
    exact (hv v).2 i (fun h => (Nat.not_lt_of_ge hi) ((slot_exists M v i).mp h))

end MapLabelTests
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
