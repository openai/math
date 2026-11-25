import OAI.Computability.BorderVNP.CubePhysicalPaddingRank
import OAI.Computability.BorderVNP.CubeCableChoice
import OAI.Computability.BorderVNP.CubeGroupLoad

/-! # Translating balanced bit loads to the public interval capacities

The finite bit indicators in Lemma 8.2 count the exact live integer width
in the corresponding interval, including the bin with equal labels.
Rounding to the paper's next multiple of the fixed cube block width gives
a common capacity for every bin.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

variable {E C L : Type*} {m : ℕ}

/-- Public ordered pair of labels of a numbered cable. -/
def cablePair (ord : E ≃ Fin m) (src dst : E → C) (label : C → L) (i : Fin m) : L × L :=
  (label (src (ord.symm i)), label (dst (ord.symm i)))

/-- The balancing scan counts precisely the occupied interval positions. -/
theorem load_eq_balancing [Fintype E] [Fintype C] [DecidableEq C] [DecidableEq L]
    (ord : E ≃ Fin m) (src dst : E → C) (width : E → ℕ) (label : C → L)
    (distinct : ∀ e, src e ≠ dst e) (u v : L) :
    (load (cablePair ord src dst label) (width ∘ ord.symm) (u,v) : ℝ) =
      Balancing.load (Balancing.cable (fun b : Balancing.Bits width => src b.1)
        (fun b : Balancing.Bits width => dst b.1) u v) label := by
  let f (e : E) : ℝ := if label (src e) = u ∧ label (dst e) = v then 1 else 0
  have hh (b : Balancing.Bits width) :
      Balancing.hit (Balancing.cable (fun b : Balancing.Bits width => src b.1)
        (fun b : Balancing.Bits width => dst b.1) u v b) label = f b.1 := by
    simp [Balancing.hit, Balancing.cable, f, (distinct b.1).symm]
  rw [Balancing.load]
  simp only [hh]
  rw [Balancing.sum_bits width f]
  unfold load
  rw [Nat.cast_sum]
  apply Fintype.sum_equiv ord.symm
  intro i
  by_cases h : label (src (ord.symm i)) = u ∧ label (dst (ord.symm i)) = v <;>
    simp [binWidth, cablePair, f, h]

/-- Number of consecutive blocks in each ordered pair as in §8.2. -/
noncomputable def blocksFor (W : ℝ) (bc Z : ℕ) : ℕ := ⌈4*W/(bc*Z^2 : ℕ)⌉₊

/-- Rounding the public upper bound on the count provides the exact common
physical capacity needed by the interval embedding. -/
theorem load_le_blocks [Fintype E] [Fintype C] [DecidableEq C] [DecidableEq L]
    (ord : E ≃ Fin m) (src dst : E → C) (width : E → ℕ) (label : C → L)
    (distinct : ∀ e, src e ≠ dst e) {W : ℝ} (hW : 0 ≤ W) {bc Z : ℕ}
    (hb : 0 < bc) (hZ : 0 < Z)
    (balanced : ∀ u v, Balancing.load (Balancing.cable
      (fun b : Balancing.Bits width => src b.1) (fun b : Balancing.Bits width => dst b.1) u v)
      label ≤ 4*W/(Z : ℝ)^2) (p : L × L) :
    load (cablePair ord src dst label) (width ∘ ord.symm) p ≤ blocksFor W bc Z * bc := by
  rcases p with ⟨u,v⟩
  have hcap : 4*W/(Z:ℝ)^2 ≤ (pairWidth W bc Z : ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (pairWidth_bounds hW hb hZ).1
  have h := (load_eq_balancing ord src dst width label distinct u v).le.trans ((balanced u v).trans hcap)
  rw [pairWidth, Nat.mul_comm bc] at h
  exact_mod_cast h

/-- The load bound survives decoding integer label codes into their product
alphabet. Distinctness is required of the cells, not of their assigned labels. -/
theorem balanced_decode [Fintype E] [Fintype C] [DecidableEq C] [DecidableEq L]
    {A : Type*} [DecidableEq A] (decode : A ≃ L) (src dst : E → C) (width : E → ℕ)
    (code : C → A) (distinct : ∀ e, src e ≠ dst e) (bound : ℝ)
    (balanced : ∀ u v, Balancing.load (Balancing.cable
      (fun b : Balancing.Bits width => src b.1) (fun b : Balancing.Bits width => dst b.1) u v)
      code ≤ bound) (u v : L) :
    Balancing.load (Balancing.cable (fun b : Balancing.Bits width => src b.1)
      (fun b : Balancing.Bits width => dst b.1) u v) (decode ∘ code) ≤ bound := by
  have ord := Fintype.equivFin E
  rw [← load_eq_balancing ord _ _ _ _ distinct]
  have h := balanced (decode.symm u) (decode.symm v)
  rw [← load_eq_balancing ord _ _ _ _ distinct] at h
  simpa only [load, binWidth, cablePair, Function.comp_apply, Prod.mk.injEq,
    ← Equiv.eq_symm_apply] using h

end Cube.Physical

end BorderVNP
end Computability
end OAI
