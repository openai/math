import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPartition
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! # Locality of planar patch selection

The boundary tests inspect both endpoints of every incident edge, including
edges with the same endpoints. A radius of `2 * K + 1` therefore suffices to
decide whether a specified patch containing the root is selected in a round.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V E : Type*} {tail head : E → V}

/-- Distances between vertices of a connected patch are bounded by a simple
path inside it. -/
theorem Connected.edist_lt_card {P : Finset V} (hP : Connected tail head P)
    {x y : V} (hx : x ∈ P) (hy : y ∈ P) :
    (underlying tail head).edist x y < P.card := by
  classical
  let G := underlying tail head
  obtain ⟨p, hp⟩ := SimpleGraph.Connected.exists_isPath hP ⟨x, hx⟩ ⟨y, hy⟩
  have hlen : p.length < P.card := by simpa using hp.length_lt
  have hdist := SimpleGraph.edist_le (p.map (SimpleGraph.Embedding.induce (G := G) (P : Set V)).toHom)
  rw [SimpleGraph.Walk.length_map] at hdist
  exact lt_of_le_of_lt hdist (by exact_mod_cast hlen)

/-- Every edge's two endpoints in the underlying graph have distance at most one. -/
theorem edist_endpoints_le_one (tail head : E → V) (e : E) :
    (underlying tail head).edist (tail e) (head e) ≤ 1 := by
  apply SimpleGraph.edist_le_one_iff_adj_or_eq.mpr
  by_cases h : tail e = head e
  · exact Or.inr h
  · exact Or.inl ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩

/-- Agreement of two purported remaining vertex sets on a closed graph ball. -/
def AgreeOnBall (G : SimpleGraph V) (x : V) (n : ℕ) (R S : Finset V) : Prop :=
  ∀ y, G.edist x y ≤ n → (y ∈ R ↔ y ∈ S)

theorem AgreeOnBall.symm {G : SimpleGraph V} {x : V} {n : ℕ} {R S : Finset V}
    (h : AgreeOnBall G x n R S) : AgreeOnBall G x n S R :=
  fun y hy => (h y hy).symm

private theorem edist_le_add {G : SimpleGraph V} {x y z : V} {a b : ℕ}
    (hxy : G.edist x y ≤ a) (hyz : G.edist y z ≤ b) : G.edist x z ≤ (↑(a+b) : ℕ∞) := by
  rw [Nat.cast_add]
  exact SimpleGraph.edist_triangle.trans (add_le_add hxy hyz)

variable [DecidableEq V] [Fintype E]

/-- The edge boundary of a patch is determined by the remaining vertices one
step beyond the ball containing the patch. -/
theorem boundary_eq_of_agreeOnBall {x : V} {r : ℕ} {P R S : Finset V}
    (hP : ∀ y ∈ P, (underlying tail head).edist x y ≤ r)
    (h : AgreeOnBall (underlying tail head) x (r+1) R S) :
    boundary tail head R P = boundary tail head S P := by
  ext e
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  have hd := edist_endpoints_le_one tail head e
  have hrev := hd
  rw [SimpleGraph.edist_comm] at hrev
  have hh (ht : tail e ∈ P) := h (head e) (edist_le_add (b := 1) (hP _ ht) hd)
  have ht (hh : head e ∈ P) := h (tail e) (edist_le_add (b := 1) (hP _ hh) hrev)
  grind

/-- A candidate lying in the radius-`r` ball transfers to any remainder
agreeing out to radius `r+1`. -/
theorem Candidate.of_agreeOnBall {x : V} {K r : ℕ} {ε : ℝ} {P R S : Finset V}
    (hP : Candidate tail head K ε R P)
    (hball : ∀ y ∈ P, (underlying tail head).edist x y ≤ r)
    (h : AgreeOnBall (underlying tail head) x (r+1) R S) :
    Candidate tail head K ε S P := by
  refine ⟨hP.1, ?_, hP.2.2.1, hP.2.2.2.1, ?_⟩
  · intro y hy
    exact (h y ((hball y hy).trans (by exact_mod_cast Nat.le_succ r))).mp (hP.2.1 hy)
  · rw [← boundary_eq_of_agreeOnBall hball h]
    exact hP.2.2.2.2

/-- A candidate has intrinsic diameter strictly below its cardinality, so its
vertices lie within distance `K` of any one of them. -/
theorem Candidate.edist_le {K : ℕ} {ε : ℝ} {R P : Finset V}
    (hP : Candidate tail head K ε R P) {x y : V} (hx : x ∈ P) (hy : y ∈ P) :
    (underlying tail head).edist x y ≤ K :=
  (hP.2.2.1.edist_lt_card hx hy).le.trans (by exact_mod_cast hP.2.2.2.1)

omit [DecidableEq V] in
private theorem nameList_congr {key key' : V ↪ ℕ} {P : Finset V}
    (h : ∀ y ∈ P, key y = key' y) : nameList key P = nameList key' P := by
  have he : P.map key = P.map key' := by
    ext n
    simp only [Finset.mem_map]
    exact ⟨fun ⟨v, hv, hn⟩ => ⟨v, hv, (h v hv).symm.trans hn⟩,
      fun ⟨v, hv, hn⟩ => ⟨v, hv, (h v hv).trans hn⟩⟩
  simp only [nameList, he]

/-- The names used to compare two intersecting candidates lie within radius
`2K` of the vertex being checked. The remaining flags needed to count their
boundary edges lie within radius `2K+1`. -/
theorem roundSelected_congr_of_local_data {key key' : V ↪ ℕ} {K : ℕ} {ε : ℝ}
    {x : V} {P R S : Finset V} (hx : x ∈ P)
    (hnames : ∀ y, (underlying tail head).edist x y ≤ (↑(2*K) : ℕ∞) → key y = key' y)
    (h : AgreeOnBall (underlying tail head) x (2*K+1) R S) :
    P ∈ roundSelected key (candidatesOn tail head K ε) R ↔
      P ∈ roundSelected key' (candidatesOn tail head K ε) S := by
  have transfer {a b : V ↪ ℕ} {A B : Finset V}
      (hab : ∀ y, (underlying tail head).edist x y ≤ (↑(2*K) : ℕ∞) → a y = b y)
      (hAB : AgreeOnBall (underlying tail head) x (2*K+1) A B)
      (hP : P ∈ roundSelected a (candidatesOn tail head K ε) A) :
      P ∈ roundSelected b (candidatesOn tail head K ε) B := by
    have hPC := mem_candidatesOn.mp ((mem_selected a).mp hP).1
    have hballP (y) (hy : y ∈ P) : (underlying tail head).edist x y ≤ (↑(2*K) : ℕ∞) :=
      (hPC.edist_le hx hy).trans (by exact_mod_cast (by omega : K ≤ 2*K))
    apply (mem_selected b).mpr
    refine ⟨mem_candidatesOn.mpr (hPC.of_agreeOnBall hballP hAB), ?_⟩
    intro Q hQ hmeet
    have hQC := mem_candidatesOn.mp hQ
    obtain ⟨y, hyP, hyQ⟩ := Finset.not_disjoint_iff.mp hmeet
    have hballQ (z) (hz : z ∈ Q) : (underlying tail head).edist x z ≤ (↑(2*K) : ℕ∞) := by
      rw [two_mul]
      exact edist_le_add (hPC.edist_le hx hyP) (hQC.edist_le hyQ hz)
    rw [← nameList_congr (fun z hz => hab z (hballP z hz)),
      ← nameList_congr (fun z hz => hab z (hballQ z hz))]
    exact ((mem_selected a).mp hP).2 Q (mem_candidatesOn.mpr (hQC.of_agreeOnBall hballQ hAB.symm)) hmeet
  exact ⟨transfer hnames h, transfer (fun y hy => (hnames y hy).symm) h.symm⟩

/-- Agreement of the remaining vertices on the radius-`2K+1` ball preserves
the entire selected patch at the vertex. -/
theorem roundSelected_congr_of_agreeOnBall (key : V ↪ ℕ) {K : ℕ} {ε : ℝ}
    {x : V} {P R S : Finset V} (hx : x ∈ P)
    (h : AgreeOnBall (underlying tail head) x (2*K+1) R S) :
    P ∈ roundSelected key (candidatesOn tail head K ε) R ↔
      P ∈ roundSelected key (candidatesOn tail head K ε) S :=
  roundSelected_congr_of_local_data hx (fun _ _ => rfl) h

/-- Running the round on just the observed ball computes the same selection
for every patch containing its center. -/
theorem roundSelected_iff_restrict_to_ball (key : V ↪ ℕ) {K : ℕ} {ε : ℝ}
    {x : V} {P R : Finset V} (hx : x ∈ P) :
    P ∈ roundSelected key (candidatesOn tail head K ε) R ↔
      P ∈ roundSelected key (candidatesOn tail head K ε)
        (R.filter fun y => (underlying tail head).edist x y ≤ (↑(2*K+1) : ℕ∞)) := by
  classical
  apply roundSelected_congr_of_agreeOnBall key hx
  intro y hy
  exact ⟨fun hR => Finset.mem_filter.mpr ⟨hR, hy⟩, fun hR => (Finset.mem_filter.mp hR).1⟩

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
