import OAI.Computability.BorderVNP.CubeEnergy
import OAI.Computability.VPVNP.WireCATZero
import OAI.Computability.VPVNP.MotifBase

/-!
# Antipodal equality wires as ordinary sums of edge networks

This is Lemma 8.1 of the border circuit manuscript. Each supply label names a
vertex and a coordinate. Thus both orientations of an edge are available. A
selected supply has nonzero width on only its named edge. The spectral comparison
produces an ordinary sum of local linear maps, over the original coefficient field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open VPVNP VPVNP.MotifBase VPVNP.WireTensor

/-- A directed cube edge. The corresponding equality wire can be used in either orientation. -/
abbrev Edge (a : ℕ) := Vertex a × Fin a

/-- The head of a directed edge at its toggled coordinate. -/
def head {a : ℕ} (e : Edge a) := e.1 + step e.2

/-- The width profile that assigns all its bits to one edge. -/
def onEdge {a : ℕ} (s : ℕ) (e j : Edge a) : ℕ := if j = e then s else 0

private theorem colors_constant {a : ℕ} (c : Vertex a → Fin 2)
    (hedge : ∀ e : Edge a, c e.1 = c (head e)) (i j : Vertex a) : c i = c j := by
  have invariant (w : Vertex a) : ∀ x, c x = c (x+w) := by
    refine Pi.single_induction (fun w : Vertex a ↦ ∀ x, c x = c (x+w)) w ?_ ?_ ?_
    · simp
    · intro w z hw hz x
      exact (hw x).trans (by simpa only [add_assoc] using hz (x+w))
    · intro i v
      rcases (show ∀ v : ZMod 2, v = 0 ∨ v = 1 by decide) v with rfl | rfl
      · simp
      · intro x; exact hedge (x,i)
  simpa only [add_sub_cancel] using invariant (j-i) i

private theorem strict_on_edge (k : Type*) [Field k] (n b s : ℕ)
    (hs : b * ((2 : ℝ)^n * Real.sqrt (n+1)) < s) :
    StrictAtSpectrum k (@start n) (@stop n) Prod.fst head (fun _ ↦ b) (onEdge s) := by
  classical
  intro F
  let d (e : Edge (n+1)) := F.wireDistance e.1 (head e)
  obtain ⟨e, _, he⟩ := Finset.exists_max_image (Finset.univ : Finset (Edge (n+1))) d
    Finset.univ_nonempty
  have hm : 0 < d e := by
    obtain ⟨j, hj⟩ := F.exists_pos_connected_wireDistance Prod.fst head colors_constant
    exact hj.trans_le (he j (Finset.mem_univ _))
  obtain ⟨X, _, hc, f, hdist⟩ := F.catZero_embedding
  have hb := antipodal_distance_le n hc f hm.le (fun x i ↦ by
    rw [hdist]; exact he (x,i) (Finset.mem_univ _))
  simp_rw [hdist] at hb
  refine ⟨e, ?_⟩
  rw [← Finset.mul_sum]
  calc
    _ ≤ (b : ℝ) * (2^n * Real.sqrt (n+1) * d e) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ < (s : ℝ) * d e := by rw [← mul_assoc]; exact mul_lt_mul_of_pos_right hs hm
    _ = _ := by simp [onEdge, d]

/-- Arbitrarily large block widths admit the cube identity. The term index consists of
one of `K` copies and `h` edges, whose local maps appear in an ordinary sum.
Selector and edge width are bounded separately as in Lemma 8.1. -/
theorem antipodal_wire_identity (k : Type*) [Field k] (n B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ b h K s : ℕ, B ≤ h * b ∧ 0 < h * b ∧ 1 ≤ K ∧
      BaseIdentity k (@start n) (@stop n) Prod.fst head (fun _ ↦ b) (onEdge s) K h ∧
      (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤ η * (h*b : ℕ) ∧
      ∀ σ : Fin h → Edge (n+1), (∑ e, (payload (onEdge s) σ e : ℝ)) ≤
        2 * 2^n * Real.sqrt (n+1) * (h*b : ℕ) := by
  classical
  let A := (2 : ℝ)^n * Real.sqrt (n+1)
  have hA : 1 ≤ A := by
    apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) _
    exact (Real.one_le_sqrt).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let s₀ := ⌊A⌋₊ + 1
  have hs₀ : A < (s₀ : ℝ) := by
    simpa only [s₀, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one A
  have hupper : (s₀ : ℝ) ≤ 2 * A := by
    simp only [s₀, Nat.cast_add, Nat.cast_one]
    linarith only [Nat.floor_le (zero_le_one.trans hA), hA]
  let width (t : ℕ) := t * (B+1)
  have identities (t : ℕ) : ∃ K : ℕ, 1 ≤ K ∧
      (0 < t → ∀ h, BaseIdentity k (@start n) (@stop n) Prod.fst head
        (fun _ ↦ width t) (onEdge (width t * s₀)) K h) := by
    by_cases ht : 0 < t
    · have hw : 0 < width t := Nat.mul_pos ht (by omega)
      have hs : (width t : ℝ) * A < (width t * s₀ : ℕ) := by
        exact_mod_cast (mul_lt_mul_of_pos_left hs₀ (Nat.cast_pos.mpr hw))
      obtain ⟨K, hK, hid⟩ := uniform_base_identity (@start n) (@stop n) Prod.fst head
        (fun _ : Unit ↦ fun _ ↦ width t) (onEdge (width t * s₀))
        (fun _ ↦ strict_on_edge k n _ _ hs)
      exact ⟨K, hK, fun _ ↦ hid ()⟩
    · exact ⟨1, le_rfl, fun h ↦ (ht h).elim⟩
  choose K hK hid using identities
  obtain ⟨t, h, ht, hh, hsel⟩ := MotifWidths.exists_selector_block (B+1)
    (Fintype.card (Edge (n+1))) (by omega) K hη
  have hw : 0 < width t := Nat.mul_pos ht (by omega)
  have hbw : B ≤ width t :=
    (Nat.le_succ B).trans (Nat.le_mul_of_pos_left _ ht)
  refine ⟨width t, h, K t, width t * s₀, hbw.trans (Nat.le_mul_of_pos_left _ hh),
    Nat.mul_pos hh hw, hK t, hid t ht h, ?_, ?_⟩
  · change (MotifWidths.selectorBits _ _ _ : ℝ) ≤ η * (h * (t * (B+1)) : ℕ)
    push_cast
    simpa only [Nat.cast_add, Nat.cast_one] using ((div_lt_iff₀ (by positivity)).mp hsel).le
  · intro σ
    have total : (∑ e, payload (onEdge (width t * s₀)) σ e) = h * (width t * s₀) := by
      unfold payload
      rw [Finset.sum_comm]
      simp [onEdge]
    rw [← Nat.cast_sum, total]
    push_cast
    change (h : ℝ) * ((width t : ℝ) * s₀) ≤ _
    calc
      _ ≤ (h : ℝ) * ((width t : ℝ) * (2 * A)) := by gcongr
      _ = _ := by dsimp [A]; ring

end Cube

end BorderVNP
end Computability
end OAI
