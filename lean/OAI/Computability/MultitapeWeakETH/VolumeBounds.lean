import OAI.Computability.MultitapeWeakETH.VolumeGrid
import OAI.Computability.MultitapeWeakETH.SparseExpansion

/-! # Uniform subexponential bounds on the three different enumeration indices -/

namespace OAI.Computability.MultitapeWeakETH.DyadicBudget

open VPVNP Compression PairSimulation.LocalHistory NetworkKernel FactorizedCompression Filter
open scoped Classical
noncomputable section

variable {k R : Type} [Field k] [Field R] {S : BlockSchedule k} (B : S.Templates)
    (f : B.Entry → R) (hf : B.IsSolution f)

set_option maxHeartbeats 1500000 in
/-- Select the grid before the formula and bound the actual encoded history,
all shared bits, and each site's private code, using the same saving at every
sufficiently large volume. The local parser is supplied by sparse_leaf_parsers. -/
theorem enumeration_bits :
    let K := stepSize B
    let b := 4*K
    ∀ᶠ N : ℕ in atTop,
      let s := index b N
      let u := K*s
      let budget := (N:ℝ)^(1-1/(2*b:ℝ))
      ∀ (X : State (S.degreeExponent 0) (3*u)),
        X.positions = (8*u+4)*2^(3*u) → X.maxWireWidth ≤ 2^(u+2) →
        ∀ (z : (B.execute f hf s (lanes_fit B s) X).Choices),
          (((executeOuterReader B f hf s (lanes_fit B s) X).encode z).length : ℝ) ≤ budget ∧
          (((B.execute f hf s (lanes_fit B s) X).finalState z).totalWidth : ℝ) ≤ budget ∧
          ((B.growthConstant^s * (B.growthConstant^s * (X.maxWireWidth+1)) : ℕ) : ℝ) ≤ budget ∧
          ∀ (P : SiteParsers f X.network), (∀ v a c, ((P.read v a).encode c).length = 0) →
          let E := B.execute f hf s (lanes_fit B s) X
          let Q := finalParsers (E.termChain (B.records f hf s (lanes_fit B s) X) z)
            (selectedParsers B f hf s (lanes_fit B s) X z) P
          ∀ v a c, (((Q.read v a).encode c).length : ℝ) ≤ budget := by
  let K := stepSize B
  let b := 4*K
  let d := (2:ℝ)^S.degreeExponent 0
  let C := scanConstant B
  let A := (S.steps+1)*(8*K+4)*C*(C+2*K+4)
  have hK : 1 ≤ K := step_pos B
  have hb : 1 < b := by dsimp [b]; omega
  have hcoeff : 0 ≤ 4*d+B.widthAllowance := by
    have := Real.sqrt_nonneg (B.procedure B.exists_solution.choose B.exists_solution.choose_spec).potentialWeight
    dsimp [d,BlockSchedule.Templates.widthAllowance]; positivity
  have sel := eventually_grid_saving hb (A:ℝ) (by positivity) 3
  have sh := eventually_grid_saving hb ((8*(K:ℝ)+4)*(4*d+B.widthAllowance)) (by positivity) 1
  have loc := eventually_grid_saving hb 8 (by norm_num) 0
  filter_upwards [sel,sh,loc] with N sel sh loc
  dsimp only
  intro X pos width z
  let s := index b N
  let u := K*s
  have exp : 4*u-s = (b-1)*s := by
    dsimp only [u,b]; rw [Nat.sub_mul,Nat.one_mul,Nat.mul_assoc]
  have h3 : 3*u ≤ (b-1)*s := by
    have : s ≤ u := Nat.le_mul_of_pos_left _ hK
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) h3
  have pbound : 8*u+4 ≤ (8*K+4)*(s+1) := by dsimp [u]; nlinarith
  have cbound : C+(2*u+4) ≤ (C+2*K+4)*(s+1) := by dsimp [u]; nlinarith
  constructor
  · have count := (executeOuterReader_bits_le B f hf s (lanes_fit B s) X z).trans
        (selector_bits B s X width)
    rw [pos] at count
    have natbound : ((S.steps+1)*s)*(((8*u+4)*2^(3*u))*C*(C+(2*u+4))) ≤
        A*(s+1)^3*2^((b-1)*s) := by
      calc
        _ ≤ ((S.steps+1)*(s+1))*((((8*K+4)*(s+1))*2^((b-1)*s))*C*((C+2*K+4)*(s+1))) := by gcongr; omega
        _ = _ := by dsimp [A]; ring
    exact (show (_:ℝ) ≤ (A:ℝ)*((s:ℝ)+1)^3*2^((b-1)*s) by exact_mod_cast count.trans natbound).trans sel
  constructor
  · have cost := shared_bits B f hf s X width pos z
    change _ ≤ (8*(u:ℝ)+4)*(4*d+B.widthAllowance)*(2:ℝ)^(4*u-s) at cost
    rw [exp] at cost
    apply cost.trans
    apply le_trans _ sh
    rw [pow_one]
    have h : 8*(u:ℝ)+4 ≤ (8*(K:ℝ)+4)*((s:ℝ)+1) := by exact_mod_cast pbound
    calc
      _ ≤ ((8*(K:ℝ)+4)*((s:ℝ)+1))*(4*d+B.widthAllowance)*2^((b-1)*s) := by gcongr
      _ = _ := by ring
  · suffices localCap : ((B.growthConstant^s * (B.growthConstant^s * (X.maxWireWidth+1)) : ℕ) : ℝ) ≤
        (N:ℝ)^(1-1/(2*b:ℝ)) by
      refine ⟨localCap,?_⟩
      intro P leaf v a c
      have read := selectedSite_length_le B f hf s (lanes_fit B s) X z P 0
        (fun i h c => (leaf i h c).le) v a c
      rw [Nat.zero_max] at read
      exact (Nat.cast_le.mpr read).trans localCap
    have bound := private_bits B s X width
    change _ ≤ 2^(3*u+3) at bound
    rw [pow_add] at bound
    have mul : 2^(3*u)*2^3 ≤ 8*2^((b-1)*s) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hpow
    exact (show (_:ℝ) ≤ 8*(2:ℝ)^((b-1)*s) by exact_mod_cast bound.trans mul).trans (by simpa only [pow_zero,mul_one] using loc)

end
end OAI.Computability.MultitapeWeakETH.DyadicBudget
