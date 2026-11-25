import OAI.Computability.BorderVNP.RoutingISAScheduleClockPhases

/-! # One set of integer phase windows shared by all evaluating histories

Rounding the uniform public and local scales before selecting a geometry
history allows the pre-call and post-call maxima to be reached on different
private choices. The resulting sum still fits the physical global clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open TeamScales Filter

/-- History-independent integer windows at the exact points used by the
signed body. The two uses of the batch-sized residue allowance bound the
rectangular tally work and the lead reader independently. -/
def uniformWindows (r R X P L K fixed F H : ℕ) : PhaseCharges :=
  ⟨2048*(X+(R+1)^3+2*P+r+1),
    4096*P+K*L,
    (8192+fixed)*P+(1400001000+2*F)*L,
    65*P+(64+2*F+128*H)*L+r,r⟩

/-- All five finite phase allowances of any one physical layout fit the
same five integer windows. The hypotheses bound the inputs, loops and
physical field counts and apply unchanged on other accepted layouts. -/
theorem phaseCharges_le_uniform {r R X P L K fixed F H : ℕ}
    {core geometry V entries cells bundles output desc decl cables U w words powers rectangle reader : ℕ}
    (publicPos : 1 ≤ P) (coreFit : core ≤ 2048*(X+(R+1)^3+2*P+r+1))
    (geometryFit : geometry ≤ P) (reserve : R*V ≤ P) (privateRows : entries ≤ R*V)
    (cellFit : cells ≤ output) (bundlesFit : bundles ≤ output) (outFit : output ≤ P)
    (descFit : desc ≤ P) (declFit : decl ≤ K*L) (cableFit : 82*cables ≤ 4*P)
    (cubeFit : U ≤ 2*L) (wordFit : (w+1)*words ≤ P) (exteriorFit : (w+1)*X ≤ 2*L)
    (powerFit : powers ≤ L) (rectFit : rectangle ≤ r) (readerFit : reader ≤ r) :
    let c := phaseCharges core geometry fixed R V entries cells bundles desc decl cables U F H w words powers X rectangle reader
    let u := uniformWindows r R X P L K fixed F H
    c.core ≤ u.core ∧ c.before ≤ u.before ∧ c.argumentsCalls ≤ u.argumentsCalls ∧ c.finish ≤ u.finish ∧ c.reader ≤ u.reader := by
  dsimp only [phaseCharges,uniformWindows]
  have h := directoryWork_le privateRows cellFit bundlesFit
  have split : directoryWork R V entries cells bundles =
      beforeDirectory R V entries+argumentDirectory cells bundles := by
    unfold directoryWork beforeDirectory argumentDirectory
    omega
  rw [split] at h
  have dir : beforeDirectory R V entries+argumentDirectory cells bundles ≤ 3072*P := by omega
  have base : words ≤ P := (show words ≤ (w+1)*words from Nat.le_mul_of_pos_left _ (by omega)).trans wordFit
  have const := Nat.le_mul_of_pos_right fixed publicPos
  have f := Nat.mul_le_mul_left F cubeFit
  have h' := Nat.mul_le_mul_left H cubeFit
  have ff : F*(2*L) = 2*F*L := by ring
  have hh : H*(2*L) = 2*H*L := by ring
  rw [ff] at f
  rw [hh] at h'
  unfold cellWork
  simp only [Nat.add_mul,Nat.mul_assoc,one_mul] at wordFit exteriorFit f h' ⊢
  omega

/-- The exact rounded windows precede the geometry, choice tape, and
per-cell inputs. Their sum fits the single tick bound uniformly in the
allowed batch and team counts. -/
theorem eventually_uniformWindows (a D K fixed F H : ℕ) (ha : 1 ≤ a) {α ξ : ℝ}
    (hα : 0 ≤ α) (small : α*a < 1/10^6) (hξ : 0 < ξ) (hξ' : ξ < 1/25) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r R : ℕ, 1 ≤ r → 1 ≤ R →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → (R:ℝ) ≤ (n:ℝ)^(2*α) →
      let c := uniformWindows r R (exterior ξ r n) ⌈publicWork a α r n R⌉₊
        ⌈localWork a D α ξ r n R⌉₊ K fixed F H
      c.core+c.before+c.argumentsCalls+c.finish+c.reader ≤ ticks ξ r n := by
  obtain ⟨ω,hω,h⟩ := eventually_mixedClock a D ha hα small hξ hξ'
  let C : ℝ := 3000000000+2*K+2*fixed+8*F+256*H
  refine ⟨ω,hω,?_⟩
  filter_upwards [h 4 C (by norm_num) (by dsimp [C]; positivity),eventually_ge_atTop 1] with n clock hn
  intro r R hr hR batch teams c
  let P := publicWork a α r n R
  let L := localWork a D α ξ r n R
  have npos : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have rpos : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have Rpos : 1 ≤ (R:ℝ) := by exact_mod_cast hR
  have rP : (r:ℝ) ≤ P := by
    have b := mul_le_mul_of_nonneg_left (Real.one_le_rpow npos (by norm_num : 0≤(19/20:ℝ))) (Nat.cast_nonneg r)
    rw [mul_one] at b
    dsimp [P,publicWork]; linarith [show 0 ≤ ((Routing.labelCount a α n:ℝ)+R)^10 by positivity]
  have oneP := rpos.trans rP
  have oneL : 1 ≤ L := by
    have table := one_le_pow₀ (n:=10) (show 1 ≤ (Routing.labelCount a α n:ℝ)+R by
      linarith [Nat.cast_nonneg (α:=ℝ) (Routing.labelCount a α n)])
    exact one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α:=ℝ) (exterior ξ r n)])
      (one_le_pow₀ (by exact_mod_cast (GeometryAdviceRate.indexWidths hr hn).1))
  have ceil (x : ℝ) (hx : 1 ≤ x) : (⌈x⌉₊:ℝ) ≤ 2*x := by
    have b := Nat.ceil_lt_add_one (zero_le_one.trans hx); linarith
  have pcap := ceil P oneP
  have lcap := ceil L oneL
  let pC : ℝ := 4096+8192+fixed+65
  let lC : ℝ := K+(1400001000+2*F)+(64+2*F+128*H)
  have pc := mul_le_mul_of_nonneg_left pcap (show 0 ≤ pC by dsimp [pC]; positivity)
  have lc := mul_le_mul_of_nonneg_left lcap (show 0 ≤ lC by dsimp [lC]; positivity)
  apply clock r R (2*⌈P⌉₊) c.core _ hr hR batch teams (by rfl)
  · change ((2*⌈P⌉₊:ℕ):ℝ) ≤ 4*P
    push_cast; linarith
  · push_cast
    change (c.core+c.before+c.argumentsCalls+c.finish+c.reader:ℝ) ≤ c.core+C*(P+L)
    have shape : (c.before+c.argumentsCalls+c.finish+c.reader:ℝ) =
        pC*(⌈P⌉₊:ℝ)+lC*(⌈L⌉₊:ℝ)+2*r := by
      dsimp [c,uniformWindows,P,L,pC,lC]; push_cast; ring
    have pCoeff : 2*pC+2 ≤ C := by dsimp [pC,C]; linarith [Nat.cast_nonneg (α:=ℝ) K,Nat.cast_nonneg (α:=ℝ) F,Nat.cast_nonneg (α:=ℝ) H]
    have lCoeff : 2*lC ≤ C := by dsimp [lC,C]; linarith [Nat.cast_nonneg (α:=ℝ) fixed]
    have pMax := mul_le_mul_of_nonneg_right pCoeff (zero_le_one.trans oneP)
    have lMax := mul_le_mul_of_nonneg_right lCoeff (zero_le_one.trans oneL)
    linarith only [shape,pc,lc,rP,pMax,lMax]

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
