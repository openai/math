import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-! # Completing noncrossing wires to a triangulation

A triangulation rooted at the closing polygon side splits a vertex interval
at a third corner. The maximal neighbour of the left endpoint determines a
split such that every prescribed chord belongs to one of the two intervals.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

open Finset

/-- The rooted dual of a triangulation, including the polygon sides as leaves. -/
inductive Triangulation : ℕ → ℕ → Type
  | side (lo : ℕ) : Triangulation lo (lo+1)
  | split {lo mid hi : ℕ} (h₁ : lo < mid) (h₂ : mid < hi)
      (left : Triangulation lo mid) (right : Triangulation mid hi) : Triangulation lo hi

namespace Triangulation

/-- Sorted vertex pairs of every rooted side, both boundary and internal. -/
def edges {lo hi : ℕ} (T : Triangulation lo hi) : Finset (ℕ × ℕ) :=
  match T with
  | .side lo => {(lo, lo+1)}
  | .split (lo := lo) (hi := hi) _ _ left right => insert (lo,hi) (left.edges ∪ right.edges)

def HasEdge {lo hi : ℕ} (T : Triangulation lo hi) (a b : ℕ) := (a,b) ∈ T.edges

theorem mem_edges {lo hi a b : ℕ} {T : Triangulation lo hi} :
    (a,b) ∈ T.edges ↔ T.HasEdge a b := Iff.rfl

@[simp] theorem side_hasEdge {lo a b : ℕ} :
    (side lo).HasEdge a b ↔ a=lo ∧ b=lo+1 := by simp [HasEdge, edges]

@[simp] theorem split_hasEdge {lo mid hi a b : ℕ} {hl : lo < mid} {hr : mid < hi}
    {l : Triangulation lo mid} {r : Triangulation mid hi} :
    (split hl hr l r).HasEdge a b ↔ (a=lo ∧ b=hi) ∨ l.HasEdge a b ∨ r.HasEdge a b := by
  simp [HasEdge, edges]

@[simp] theorem root_mem {lo hi : ℕ} (T : Triangulation lo hi) : (lo,hi) ∈ T.edges := by
  cases T <;> simp [edges]

theorem bounds_of_mem_edges {lo hi a b : ℕ} (T : Triangulation lo hi)
    (h : (a,b) ∈ T.edges) : lo ≤ a ∧ a < b ∧ b ≤ hi := by
  induction T with
  | side lo =>
    obtain ⟨rfl,rfl⟩ := side_hasEdge.mp h
    omega
  | split hl hr l r ihl ihr =>
    rcases split_hasEdge.mp h with ⟨rfl,rfl⟩ | hx | hx
    · omega
    · obtain ⟨_,_,_⟩ := ihl hx
      omega
    · obtain ⟨_,_,_⟩ := ihr hx
      omega

/-- The two recursive edge sets are disjoint, so each prescribed wire has
a unique node to which its equality test can be assigned. -/
theorem disjoint_branches {lo mid hi : ℕ} (l : Triangulation lo mid) (r : Triangulation mid hi) :
    Disjoint l.edges r.edges := by
  apply disjoint_left.mpr
  rintro ⟨a,b⟩ hl hr
  have := l.bounds_of_mem_edges hl
  have := r.bounds_of_mem_edges hr
  omega

end Triangulation

/-- Every set of noncrossing sorted chords in an interval is contained in
a rooted triangulation on that same vertex order. -/
theorem exists_triangulation (W : ℕ → ℕ → Prop)
    (hW : ∀ a b c d, W a c → W b d → a<b → b<c → c<d → False)
    (lo hi : ℕ) (h : lo < hi) :
    ∃ T : Triangulation lo hi, ∀ a b, lo ≤ a → a < b → b ≤ hi → W a b → T.HasEdge a b := by
  classical
  by_cases he : hi = lo+1
  · subst hi
    refine ⟨.side lo, fun a b ha hab hb _ ↦ Triangulation.side_hasEdge.mpr ?_⟩
    omega
  let S := (range hi).filter (fun v ↦ lo < v ∧ (v=lo+1 ∨ W lo v))
  have hs : lo+1 ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), by simp⟩
  let m := S.max' ⟨_,hs⟩
  obtain ⟨hmt, hlm, hmW⟩ := mem_filter.mp (S.max'_mem ⟨_,hs⟩)
  have hml : lo < m := hlm
  have hmr : m < hi := mem_range.mp hmt
  obtain ⟨l,hl⟩ := exists_triangulation W hW lo m hml
  obtain ⟨r,hr⟩ := exists_triangulation W hW m hi hmr
  refine ⟨.split hml hmr l r, fun a b ha hab hb hw ↦ Triangulation.split_hasEdge.mpr ?_⟩
  by_cases he : a=lo ∧ b=hi
  · exact Or.inl he
  by_cases hb' : b ≤ m
  · exact Or.inr (Or.inl (hl _ _ ha hab hb' hw))
  by_cases ha' : m ≤ a
  · exact Or.inr (Or.inr (hr _ _ ha' hab hb hw))
  exfalso
  by_cases hal : a=lo
  · subst a
    apply hb'
    apply S.le_max'
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hab, Or.inr hw⟩
  · change m = lo+1 ∨ W lo m at hmW
    rcases hmW with he | hmW
    · omega
    · exact hW lo a m b hmW hw (by omega) (by omega) (by omega)
termination_by hi-lo
decreasing_by
  · change m - lo < hi - lo
    omega
  · change hi - m < hi - lo
    omega

/-- Complete the positive-width wires of a polygon whose ordered vertices are
indexed by `Fin k`. The closing side runs from vertex zero to vertex `k-1`. -/
theorem exists_triangulation_fin {k : ℕ} (hk : 2 ≤ k) (W : Fin k → Fin k → Prop)
    (hW : ∀ a b c d, W a c → W b d → a<b → b<c → c<d → False) :
    ∃ T : Triangulation 0 (k-1), ∀ a b : Fin k, a < b → W a b → T.HasEdge a.val b.val := by
  let E (a b : ℕ) := ∃ x y : Fin k, x.val = a ∧ y.val = b ∧ W x y
  have hE (a b c d : ℕ) (hac : E a c) (hbd : E b d) (hab : a<b) (hbc : b<c)
      (hcd : c<d) : False := by
    obtain ⟨p,r,rfl,rfl,hpr⟩ := hac
    obtain ⟨q,s,rfl,rfl,hqs⟩ := hbd
    exact hW p q r s hpr hqs hab hbc hcd
  obtain ⟨T,hT⟩ := exists_triangulation E hE 0 (k-1) (by omega)
  exact ⟨T, fun a b hab h ↦ hT _ _ (Nat.zero_le _) hab (by have := b.isLt; omega)
    ⟨a,b,rfl,rfl,h⟩⟩

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
