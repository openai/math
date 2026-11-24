import OAI.Computability.VPVNP.CursorBranchBudget

/-!
# External accesses for the compressed pair

The site burst follows its placement history and reads both of its
incidences. Summing these reads charges each final arc exactly twice,
including when its endpoints coincide. The global allowance accounts
separately for the descriptor scans, the writes of shared bits and
the final vertex visits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open Filter Compression CursorBounds

variable {k : Type*} [Field k] {S : BlockSchedule k}

/-- Total number of incident payload bits at one site, summing all incoming and outgoing
half-wire widths. -/
def incidentBits {a g : ℕ} (X : State a g) (v : X.network.Site) : ℕ :=
  ∑ dir : Bool, ∑ j, X.halfWidth v dir j

theorem incidentBits_le {a g : ℕ} (X : State a g) (v : X.network.Site) :
    incidentBits X v ≤ (2 * 2^a) * X.maxWireWidth := by
  calc _ ≤ ∑ _dir : Bool, ∑ _j : Fin (2^a), X.maxWireWidth :=
          Finset.sum_le_sum fun dir _ => Finset.sum_le_sum fun j _ => X.halfWidth_le_max v dir j
       _ = _ := by simp [Nat.mul_assoc]

/-- The two endpoint reads at all vertices together have cost twice
the total actual width. -/
theorem sum_incidentBits {a g : ℕ} (X : State a g) :
    ∑ v, incidentBits X v = 2 * X.totalWidth := by
  let e : X.network.Site × Fin (2^a) ≃ (X.Base × Fin (2^a)) × BitWord g :=
    ⟨fun x => ((x.1.1,x.2),x.1.2), fun x => ((x.1.1,x.2),x.1.2), fun _ => rfl, fun _ => rfl⟩
  have ho : ∑ v, ∑ j, X.halfWidth v false j = X.totalWidth := by
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  have hi : ∑ v, ∑ j, X.halfWidth v true j = X.totalWidth := by
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (e.trans X.slots.actualTarget.symm) _ _ fun _ => rfl
  simp only [incidentBits, Fintype.sum_bool, Finset.sum_add_distrib, ho, hi, two_mul]

/-- The per-site external charge, allowing a fixed number of probes per
incident bit, and a fixed polylogarithmic cost per history occurrence. -/
noncomputable def siteAccesses {A : Type*} {N : NetworkKernel.Network} {a g : ℕ}
    (Y : State a g) (chain : NetworkKernel.TermChain A N Y.network)
    (C logPower n : ℕ) (v : Y.network.Site) : ℕ :=
  C * (1 + incidentBits Y v + chain.occurrences (fun _ => 1) v * (n.log2+1)^logPower)

/-- Descriptor scans use old positions, final guesses use actual wire
widths, and each final-site charge uses that site's own incidences. -/
noncomputable def branchAccesses {A : Type*} {a g a' g' : ℕ} (X : State a g)
    (Y : State a' g') (chain : NetworkKernel.TermChain A X.network Y.network) (C logPower n : ℕ) :
    ℕ :=
  C * (X.positions * (n.log2+1)^logPower + Y.totalWidth) +
    ∑ v, siteAccesses Y chain C logPower n v

theorem branchAccesses_eq {A : Type*} {a g a' g' : ℕ} (X : State a g)
    (Y : State a' g') (chain : NetworkKernel.TermChain A X.network Y.network) (C logPower n : ℕ) :
    branchAccesses X Y chain C logPower n =
      C * (X.positions * (n.log2+1)^logPower + 3 * Y.totalWidth + Y.positions +
        totalOccurrences chain * (n.log2+1)^logPower) := by
  unfold branchAccesses siteAccesses totalOccurrences
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, sum_incidentBits, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  change C * (X.positions * _ + Y.totalWidth) + C * (Y.positions + 2 * Y.totalWidth + _) = _
  ring

/-- The threshold precedes every choice of branch. The total charge
fits any positive fraction of the live group, while each site's burst
is bounded by the square root of the input length. -/
theorem eventually_pairAccesses (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) (C logPower : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        ∀ z : E.Choices,
          let Y := E.finalState z
          let chain := E.termChain (B.records f hf T hT X) z
          (branchAccesses X Y chain C logPower n : ℝ) <
            ε * (processorCount b n : ℝ) * liveBucket u.δ n ∧
          (∀ v, (siteAccesses Y chain C logPower n v : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) ∧
          (n : ℝ)^(1/2 : ℝ) ≤ liveBucket u.δ n := by
  let θ := (u.θ : ℝ)
  let δ := (u.δ : ℝ)
  have ht : θ < 1/100 := by simpa [θ] using (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
  have ht0 : 0 < θ := Rat.cast_pos.mpr u.theta_pos
  have hd : δ < θ/10 := by simpa [θ,δ] using (Rat.cast_lt (K := ℝ)).mpr u.delta_lt
  let p := 2 * ((b : ℝ) + 2)
  have h₁ := eventually_absorb_polylog (3 * C * p) (2 + logPower)
    (show 3/4 + 1/100 < 1 - δ by linarith) (half_pos (half_pos hε))
  have h₂ := eventually_absorb_polylog (3 * (C : ℝ)) 0
    (show 1 - θ/2 < 1 - δ by linarith) (half_pos (half_pos hε))
  let d := (2 * S.baseDegree + 2 : ℕ)
  have hburst := eventually_burst_le (δ := δ) (by linarith) ((C : ℝ) * d) logPower
  filter_upwards [eventually_pairBranchBounds B u b hb, h₁, h₂, hburst, eventually_ge_atTop 2]
    with n hbranch h₁ h₂ hburst hn
  intro base lanes labels hD hT A _ f hf X T E z Y chain
  have h := hbranch.2.2 labels hD hT A f hf z
  let P := (initialPositions b n : ℝ)
  let R := (processorCount b n : ℝ)
  let L := ((n.log2 : ℝ) + 1)^logPower
  let g := (n : ℝ)^(1/100 : ℝ)
  let F := (Y.totalWidth : ℝ)
  have hpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hg : 1 ≤ g := Real.one_le_rpow hn1 (by norm_num)
  have hL : 1 ≤ L := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n.log2])
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hR : 0 < R := Nat.cast_pos.mpr (Nat.two_pow_pos _)
  have hw : (Y.maxWireWidth : ℝ) ≤ (n : ℝ)^(3/10 : ℝ) :=
    (Nat.cast_le.mpr h.2.2.2.2.1).trans h.2.2.2.2.2.1
  have hF : F ≤ R*(n : ℝ)^(1-θ/2) := h.2.1
  have hv : (Y.positions : ℝ) ≤ P := Nat.cast_le.mpr h.1
  have ho : (totalOccurrences chain : ℝ) ≤ P*g := h.2.2.2.2.2.2.1
  have hp := pairInput_positions S labels hD
  have hPg : P ≤ P*g := le_mul_of_one_le_right hP hg
  have hPgL : P ≤ P*g*L := hPg.trans (le_mul_of_one_le_right (by positivity) hL)
  refine ⟨?_, ?_, hburst.2⟩
  · rw [branchAccesses_eq]
    push_cast
    change (C : ℝ) * ((X.positions : ℝ)*L + 3*F + (Y.positions : ℝ) +
      (totalOccurrences chain : ℝ)*L) < ε*R*liveBucket δ n
    change X.positions = initialPositions b n at hp
    rw [hp]
    have hp' : P ≤ p*R*(n : ℝ)^(3/4 : ℝ)*((n.log2 : ℝ)+1)^2 := initialPositions_bound b n hn
    have hc : 0 ≤ (C : ℝ) := Nat.cast_nonneg _
    have hsub : P*L + 3*F + (Y.positions : ℝ) + (totalOccurrences chain : ℝ)*L ≤
        3*P*g*L + 3*(R*(n : ℝ)^(1-θ/2)) := by
      linarith only [mul_le_mul_of_nonneg_right hPg (zero_le_one.trans hL),
        mul_le_mul_of_nonneg_right ho (zero_le_one.trans hL), hv.trans hPgL, hF]
    calc _ ≤ C*(3*P*g*L + 3*(R*(n : ℝ)^(1-θ/2))) := mul_le_mul_of_nonneg_left hsub hc
         _ ≤ C*(3*(p*R*(n : ℝ)^(3/4 : ℝ)*((n.log2 : ℝ)+1)^2)*g*L +
           3*(R*(n : ℝ)^(1-θ/2))) := by gcongr
         _ = R*((3*C*p)*(n : ℝ)^(3/4+1/100 : ℝ)*((n.log2 : ℝ)+1)^(2+logPower) +
             (3*C)*(n : ℝ)^(1-θ/2)) := by rw [Real.rpow_add hpos, pow_add]; dsimp [g,L]; ring
         _ ≤ R*((ε/2/2)*(n : ℝ)^(1-δ)+(ε/2/2)*(n : ℝ)^(1-δ)) := by
           apply mul_le_mul_of_nonneg_left _ hR.le
           exact add_le_add h₁ (by simpa only [pow_zero, mul_one] using h₂)
         _ < ε * R * (n : ℝ)^(1-δ) := by
           nlinarith only [mul_pos (mul_pos hε hR) (Real.rpow_pos_of_pos hpos (1-δ))]
         _ ≤ _ := by gcongr; exact (liveBucket_bounds (by linarith : δ ≤ 1) (by omega)).1
  · intro v
    have hinc : (incidentBits Y v : ℝ) ≤ (2*S.baseDegree : ℕ) * (n : ℝ)^(3/10 : ℝ) := by
      have hi : (incidentBits Y v : ℝ) ≤ ((2*S.baseDegree : ℕ) : ℝ) * (Y.maxWireWidth : ℝ) := by
        exact_mod_cast incidentBits_le Y v
      exact hi.trans (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _))
    have hvis : (chain.occurrences (fun _ => 1) v : ℝ) ≤ g := h.2.2.1 v
    have hL' : 1 ≤ g*L := one_le_mul_of_one_le_of_one_le hg hL
    unfold siteAccesses
    push_cast
    apply le_trans _ hburst.1
    change (C : ℝ) * (1 + (incidentBits Y v : ℝ) + _*L) ≤
      ((C : ℝ)*d) * ((n : ℝ)^(3/10 : ℝ)+g*L)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    dsimp only [d]
    push_cast at hinc ⊢
    nlinarith only [hinc, mul_le_mul_of_nonneg_right hvis (zero_le_one.trans hL), hL',
      Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) (3/10),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) S.baseDegree) (zero_le_one.trans hL')]

end CursorNetwork

end VPVNP
end Computability
end OAI
