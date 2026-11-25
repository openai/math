import OAI.Hierarchy.DescentPublicDegreeNumbers
import OAI.Hierarchy.DescentHostDirectory

namespace OAI
/-! # Polynomial size and degree of the common post-subround directory -/

namespace Hierarchy.DescentHostDegree
open DescentHostDirectory
open scoped BigOperators Classical
noncomputable section

def allowedSources (Δ : ℕ) := 1+(Δ+1)*(gap Δ+1+2*2^(gap Δ))

private theorem base_lo (Δ : ℕ) : Δ≤2^logDegree Δ := by
  have h := Nat.le_pow_clog (by decide : 1<2) (2*Δ)
  change Δ≤2^Nat.clog 2 (2*Δ)
  omega

private theorem base_hi {Δ : ℕ} (positive : 0<Δ) : 2^(logDegree Δ)≤4*Δ := by
  let n := logDegree Δ
  have large : 1<2*Δ := by omega
  have prev : 2^(n-1)<2*Δ := Nat.pow_pred_clog_lt_self (by decide) large
  have pos : 0<n := Nat.clog_pos (by decide) large
  change 2^n≤4*Δ
  calc
    _ = 2^(n-1)*2 := by rw [←pow_succ];congr 1;omega
    _ ≤ _ := by omega

private theorem middle (E : ℕ) : E+1+2*2^E≤4*2^E := by
  have h : E<2^E := Nat.lt_two_pow_self
  omega

/-- Sufficient packing allowance for every old host degree. -/
theorem pack_slack (a₀ Δ : ℕ) : 2^a₀*(Δ*2^gap Δ)≤2^packExponent a₀ Δ := by
  calc
    _ ≤ 2^a₀*(2^logDegree Δ*2^gap Δ) := by gcongr;exact base_lo Δ
    _ ≤ _ := by
      rw [←pow_add,←pow_add]
      apply Nat.pow_le_pow_right (by decide)
      dsimp [packExponent,gap]
      omega

private theorem source_cap (Δ : ℕ) : allowedSources Δ≤16*2^(33*logDegree Δ) := by
  let n := logDegree Δ
  have lo : Δ≤2^n := base_lo Δ
  have pos : 0<2^n := Nat.two_pow_pos _
  have stage : (Δ+1)*(gap Δ+1+2*2^gap Δ) ≤ (2*2^n)*(4*2^gap Δ) :=
    Nat.mul_le_mul (show Δ+1≤2*2^n by omega) (middle _)
  have factor : (2*2^n)*(4*2^gap Δ)=8*2^(33*n) := by
    rw [show 33*n=n+gap Δ by dsimp [gap,n];omega,pow_add]
    ring
  rw [factor] at stage
  have h : 0<2^(33*n) := Nat.two_pow_pos _
  change 1+_≤16*2^(33*n)
  omega

/-- The same polynomial packing exponent pays the square-root and unmatched-pair
terms counted in the marked core shrink. -/
theorem pack_cutoff (Δ : ℕ) :
    481*128*((Δ+1)*(gap Δ+1+2*2^gap Δ)+1) ≤ 2^packExponent 20 Δ := by
  have h := Nat.mul_le_mul_left (481*128) (source_cap Δ)
  rw [show allowedSources Δ = (Δ+1)*(gap Δ+1+2*2^gap Δ)+1 by
    unfold allowedSources; omega] at h
  refine h.trans ?_
  change _ ≤ 2^(20+34*logDegree Δ)
  rw [pow_add,← Nat.mul_assoc]
  exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (by decide) (by omega))

/-- The common dyadic hub gain is sufficient for a thick center and all the
thin packs of every possible source colony. -/
theorem gain_covers (a₀ Δ B : ℕ) :
    2*5*((1+allowedSources Δ*(2^packExponent a₀ Δ+1))*(2^packExponent a₀ Δ*B))≤
      2^gainExponent a₀ Δ*B := by
  let a := packExponent a₀ Δ
  let K := 2^(33*logDegree Δ)
  have ak : 1≤2^a := Nat.two_pow_pos _
  have kp : 1≤K := Nat.two_pow_pos _
  have first : allowedSources Δ≤16*K := source_cap Δ
  have attached : allowedSources Δ*(2^a+1)≤32*(K*2^a) := by
    exact (Nat.mul_le_mul first (show 2^a+1≤2*2^a by omega)).trans_eq (by ring)
  have ka : 1≤K*2^a := Nat.mul_pos kp ak
  have sites : 1+allowedSources Δ*(2^a+1)≤64*(K*2^a) := by omega
  calc
    _ ≤ 2*5*((64*(K*2^a))*(2^a*B)) := by gcongr
    _ ≤ (2:ℕ)^10*(K*(2^a*2^a))*B := by
      calc
        _ = 640*(K*(2^a*2^a))*B := by ring
        _ ≤ _ := by gcongr; norm_num
    _ = _ := by
      rw [show gainExponent a₀ Δ = 10 + (33*logDegree Δ) + (a+a) by dsimp [gainExponent,a];omega]
      simp only [pow_add,K]
      ring

theorem age_le_gain (a₀ Δ : ℕ) : packExponent a₀ Δ≤gainExponent a₀ Δ := by unfold gainExponent;omega

theorem gain_poly (a₀ Δ : ℕ) (pos : 0<Δ) :
    2^gainExponent a₀ Δ≤2^(10+2*a₀)*(4*Δ)^101 := by
  rw [show gainExponent a₀ Δ=(10+2*a₀)+logDegree Δ*101 by unfold gainExponent packExponent;omega,
    pow_add,pow_mul]
  gcongr
  exact base_hi pos

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem host_positions [Fintype V] (a₀ Δ k : ℕ) (branch : 2≤Δ) :
    (keys (V:=V) k (2^packExponent a₀ Δ+2)).card≤
      Fintype.card V*2^k*(4*2^a₀*(4*Δ)^34) := by
  let a := packExponent a₀ Δ
  have npos : 0<logDegree Δ := Nat.clog_pos (by decide) (by omega)
  have ap : 1≤a := by dsimp [a,packExponent];omega
  have big : 2≤2^a := by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ap
  have idCount := keys_card (V:=V) k (2^a+2)
  have cap : 2^a≤2^a₀*(4*Δ)^34 := by
    rw [show a=a₀+logDegree Δ*34 by dsimp [a,packExponent];omega,pow_add,pow_mul]
    gcongr
    exact base_hi (by omega)
  calc
    _ ≤ Fintype.card V*2^(k+1)*(2*2^a) := idCount.trans (Nat.mul_le_mul_left _ (by omega))
    _ = Fintype.card V*2^k*(4*2^a) := by rw [pow_succ];ring
    _ ≤ _ := (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 4 cap)).trans_eq (by ring)

/-- The numerical degree of the actual common directory, at any fixed number of old-host hops. -/
theorem degree_poly (a₀ Δ h : ℕ) (branch : 2≤Δ) :
    let a := packExponent a₀ Δ
    let E := gap Δ+gainExponent a₀ Δ
    ((Δ+1)*(E+1+2*2^E)*(2^a+2))^h ≤ 2^(h*(14+3*a₀))*(4*Δ)^(168*h) := by
  dsimp only
  let n := logDegree Δ
  let a := packExponent a₀ Δ
  let E := gap Δ+gainExponent a₀ Δ
  have dl : Δ≤2^n := base_lo Δ
  have npos : 0<n := Nat.clog_pos (by decide) (by omega)
  have ap : 1≤a := by change 1≤a₀+34*n;omega
  have ab : 2≤2^a := by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ap
  have pos : 0<2^n := Nat.two_pow_pos _
  have cap : (Δ+1)*(E+1+2*2^E)*(2^a+2)≤2^(4+n+E+a) := by
    exact (Nat.mul_le_mul (Nat.mul_le_mul (show Δ+1≤2*2^n by omega) (middle E))
      (show 2^a+2≤2*2^a by omega)).trans_eq (by simp only [pow_add];ring)
  calc
    _ ≤ (2^(4+n+E+a))^h := Nat.pow_le_pow_left cap h
    _ = 2^(h*(14+3*a₀))*(2^n)^(168*h) := by
      rw [←pow_mul,←pow_mul,←pow_add]
      congr 1
      dsimp [E,gainExponent,a,packExponent,gap,n]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (base_hi (by omega)) _)

set_option exponentiation.threshold 1344 in
/-- Eight old-host hops suffice for the resolved demand and its two stars. -/
theorem post_neighbors (near : V→Finset V) (a₀ Δ : ℕ) (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ)
    (x : Key V) :
    (directory near (gap Δ+gainExponent a₀ Δ) (2^packExponent a₀ Δ+2) 8 x).card≤
      2^(8*(14+3*a₀))*(4*Δ)^1344 :=
  (directory_card near _ _ Δ degree 8 x).trans (degree_poly a₀ Δ 8 branch)

set_option exponentiation.threshold 1680 in
/-- Two additional hub coalescences give ten hops in the actual next-stage contact graph. -/
theorem coalesced_degree_poly (a₀ Δ : ℕ) (branch : 2≤Δ) :
    let a := packExponent a₀ Δ
    let E := gap Δ+gainExponent a₀ Δ
    ((Δ+1)*(E+1+2*2^E)*(2^a+2))^10≤2^(10*(14+3*a₀))*(4*Δ)^1680 :=
  degree_poly a₀ Δ 10 branch

end
end Hierarchy.DescentHostDegree

end OAI
