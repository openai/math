import OAI.Computability.BorderVNP.RoutingISAScheduleClockWindows

/-! # Actual source layouts inside the common integer phase windows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube TeamScales Filter VPVNP CellPacketGeometry

private theorem nat_le_ceiling {j : ℕ} {x : ℝ} (h : (j:ℝ) ≤ x) : j ≤ ⌈x⌉₊ :=
  (Nat.cast_le (α:=ℝ)).mp (h.trans (Nat.le_ceil x))

private theorem nat_le_multiple_ceiling {j K : ℕ} {x : ℝ} (h : (j:ℝ) ≤ K*x) : j ≤ K*⌈x⌉₊ := by
  have b := h.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil x) (Nat.cast_nonneg K))
  exact_mod_cast b

/-- Compare all five actual phase charges with the length-only windows. The
public subtotal words and output rows are measured separately, so this also
covers the signed scanner's sparse report payload. -/
theorem eventually_measuredSourceWindows {α ξ τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hξ : ξ ≤ 1)
    (a D bits B C fixed F H : ℕ) (small : α*a < 1/10^6) (alphaCap : α ≤ 1/1000)
    (hD : 1 ≤ D) (G K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K)
    (growth : τ*Real.logb 2 G ≤ α/10) (fan : τ*Real.logb 2 K ≤ α) :
    ∀ᶠ n : ℕ in atTop, ∀ (r R V z w words k u o b entries cells bundles core powers rectangle reader : ℕ)
      (l : LabelIndex.Layout) (m : ℕ → ℕ) (g : GroupWeights.Layout) (t : TeamNative.Layout) (header : HeaderDecode.Layout),
      let M := max (G^epochs τ n) (teams α τ K n)
      let Z := Routing.labelCount a α n
      let X := exterior ξ r n
      let P := publicWork a α r n R
      let L := localWork a D α ξ r n R
      let geo := GeometryAdviceRate.ticks k u o b w
      let source := phaseCharges core geo fixed R V entries cells bundles (descriptorTicks l m z a g t)
        (declarationTicks header (a-1) bits) l.cableCount (Z^2+X+1) F H w words powers X rectangle reader
      let windows := uniformWindows r R X ⌈P⌉₊ ⌈L⌉₊ (512*(a+bits+1)) fixed F H
      1 ≤ r → 1 ≤ R → R ≤ M → (V:ℝ) ≤ C*r*(n:ℝ)^(9/10:ℝ) →
      1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(M+1) → l.labels=Z → l.labels=z+1 →
      g.cells=l.cells → t.groups=g.groups → t.r+1 ≤ g.groups → g.groups ≤ l.labels →
      header.d=g.groups → header.a=a → header.cw ≤ w → header.rw ≤ w → w ≤ logWidth r n^D →
      (w+1)*words ≤ ⌈P⌉₊ → o ≤ ⌈P⌉₊ → (geo:ℝ) ≤ P →
      entries ≤ R*V → cells ≤ o → bundles ≤ o → powers ≤ r*logWidth r n → rectangle+reader ≤ r →
      core ≤ 2048*(X+(R+1)^3+(l.deliveryCount+g.groups.choose 2)+r+1) →
      source.core ≤ windows.core ∧ source.before ≤ windows.before ∧ source.argumentsCalls ≤ windows.argumentsCalls ∧
        source.finish ≤ windows.finish ∧ source.reader ≤ windows.reader := by
  filter_upwards [eventually_scheduleTicks (ξ:=ξ) hα a bits B C D small,
    MeanChoice.eventually_scanEnvelope hα a small 1 C,eventually_ge_atTop 1] with n rate grid hn
  intro r R V z w words k u o b entries cells bundles core powers rectangle reader l m g t header M Z X P L geo source windows
    hr hR RM Vcap rows ZZ hz cellsN groups team groupCount dEq axes cw rw word wordCharge out geom privateRows cellFit bundlesFit
    slots both coreCap
  have MCap := LabelIndex.multiplicity_le hn hτ alphaCap hG hK growth fan
  obtain ⟨desc,decl⟩ := rate r R V M z w l m g t header hr hR Vcap MCap rows ZZ hz cellsN groups team groupCount dEq axes cw rw word
  have descP := nat_le_ceiling desc
  change descriptorTicks l m z a g t ≤ ⌈P⌉₊ at descP
  have npos : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have rpos : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have Rpos : 1 ≤ (R:ℝ) := by exact_mod_cast hR
  have baseP : (r:ℝ)*(n:ℝ)^(19/20:ℝ) ≤ P := le_add_of_nonneg_right (by positivity)
  have oneP : 1 ≤ ⌈P⌉₊ := by
    apply nat_le_ceiling
    rw [Nat.cast_one]
    exact (one_le_mul_of_one_le_of_one_le rpos (Real.one_le_rpow npos (by norm_num : 0≤(19/20:ℝ)))).trans baseP
  have rv : R*V ≤ MeanChoice.scanEnvelope 1 V M Z := by
    have h := Nat.mul_le_mul (RM.trans (Nat.le_succ M)) (Nat.le_succ V)
    simp only [MeanChoice.scanEnvelope,one_mul]
    rw [Nat.mul_comm (V+1)]
    exact h.trans (Nat.le_mul_of_pos_right _ (pow_pos (Nat.zero_lt_succ _) _))
  have rvP := nat_le_ceiling (((Nat.cast_le (α:=ℝ)).mpr rv).trans ((grid r V M hr Vcap MCap).le.trans
    (by norm_num1; exact baseP)))
  have gP := nat_le_ceiling geom
  have tableP : l.labels^2 ≤ ⌈P⌉₊ := by
    have a₀ : (Z:ℝ) ≤ (Z:ℝ)+R := le_add_of_nonneg_right (Nat.cast_nonneg _)
    have a₁ := (pow_le_pow_left₀ (Nat.cast_nonneg _) a₀ 2).trans
      (pow_le_pow_right₀ (show 1≤(Z:ℝ)+R by linarith [Nat.cast_nonneg (α:=ℝ) Z]) (by decide : 2≤10))
    rw [ZZ]
    apply nat_le_ceiling
    push_cast
    exact a₁.trans (le_add_of_nonneg_left (by positivity))
  have data : l.deliveryCount ≤ descriptorTicks l m z a g t := by
    unfold descriptorTicks; change _ ≤ _+(41+l.deliveryCount*43+5)+_; omega
  have shared : g.groups.choose 2 ≤ l.labels^2 := by
    rw [Nat.choose_two_right,pow_two]
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul groupCount ((Nat.sub_le ..).trans groupCount))
  have capCore : core ≤ 2048*(X+(R+1)^3+2*⌈P⌉₊+r+1) := by
    have dat := data.trans descP
    have sh := shared.trans tableP
    omega
  have cU : Z^2+X+1 ≤ 2*⌈L⌉₊ := by
    apply nat_le_multiple_ceiling
    push_cast
    exact cubeUnits_le_localWork (a:=a) (D:=D) (α:=α) (ξ:=ξ) hn hr hR
  let Q := logWidth r n^D
  have qw : 1 ≤ Q := Nat.one_le_pow _ _ (GeometryAdviceRate.indexWidths hr hn).1
  have XQ : X*Q ≤ ⌈L⌉₊ := by
    apply nat_le_ceiling
    dsimp only [Q,L,localWork,X]
    push_cast
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  have xword : (w+1)*X ≤ 2*⌈L⌉₊ := by
    have bound : w+1 ≤ 2*Q := by change w ≤ Q at word; omega
    calc
      _ ≤ (2*Q)*X := Nat.mul_le_mul_right _ bound
      _ = 2*(X*Q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 XQ
  have logQ : logWidth r n ≤ Q := by
    simpa only [pow_one] using Nat.pow_le_pow_right (GeometryAdviceRate.indexWidths hr hn).1 hD
  have rX : r ≤ X := Nat.le_mul_of_pos_right _ (Nat.le_floor (by simpa using Real.one_le_rpow npos (sub_nonneg.mpr hξ)))
  exact phaseCharges_le_uniform oneP capCore gP rvP privateRows cellFit bundlesFit out descP
    (nat_le_multiple_ceiling decl) ((cableSweep_le ..).trans (Nat.mul_le_mul_left 4 descP)) cU wordCharge
    xword (slots.trans ((Nat.mul_le_mul rX logQ).trans XQ)) (by omega) (by omega)

/-- Convert the physical source scales into the five length-only windows,
including history-dependent widths, counts and allocations. The cost of
the live geometry interpreter is supplied by its gate/bit complexity
theorem and may include output columns beyond the two typed sections. -/
theorem eventually_sourceWindows {α ξ τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hξ : ξ ≤ 1)
    (a D bits B C fixed F H : ℕ) (small : α*a < 1/10^6) (alphaCap : α ≤ 1/1000)
    (hD : 1 ≤ D) (G K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K)
    (growth : τ*Real.logb 2 G ≤ α/10) (fan : τ*Real.logb 2 K ≤ α) :
    ∀ᶠ n : ℕ in atTop, ∀ (r R V z w p d k u o b entries cells bundles core powers rectangle reader : ℕ)
      (l : LabelIndex.Layout) (m : ℕ → ℕ) (g : GroupWeights.Layout) (t : TeamNative.Layout) (header : HeaderDecode.Layout),
      let M := max (G^epochs τ n) (teams α τ K n)
      let Z := Routing.labelCount a α n
      let X := exterior ξ r n
      let P := publicWork a α r n R
      let L := localWork a D α ξ r n R
      let geo := GeometryAdviceRate.ticks k u o b w
      let source := phaseCharges core geo fixed R V entries cells bundles (descriptorTicks l m z a g t)
        (declarationTicks header (a-1) bits) l.cableCount (Z^2+X+1) F H w (2^p+2^d) powers X rectangle reader
      let windows := uniformWindows r R X ⌈P⌉₊ ⌈L⌉₊ (512*(a+bits+1)) fixed F H
      1 ≤ r → 1 ≤ R → R ≤ M → (V:ℝ) ≤ C*r*(n:ℝ)^(9/10:ℝ) →
      1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(M+1) → l.labels=Z → l.labels=z+1 →
      g.cells=l.cells → t.groups=g.groups → t.r+1 ≤ g.groups → g.groups ≤ l.labels →
      header.d=g.groups → header.a=a → header.cw ≤ w → header.rw ≤ w → w ≤ logWidth r n^D →
      1 ≤ w → 1 ≤ b → Total p d ≤ o → (geo:ℝ) ≤ P →
      entries ≤ R*V → cells ≤ o → bundles ≤ o → powers ≤ r*logWidth r n → rectangle+reader ≤ r →
      core ≤ 2048*(X+(R+1)^3+(l.deliveryCount+g.groups.choose 2)+r+1) →
      source.core ≤ windows.core ∧ source.before ≤ windows.before ∧ source.argumentsCalls ≤ windows.argumentsCalls ∧
        source.finish ≤ windows.finish ∧ source.reader ≤ windows.reader := by
  filter_upwards [eventually_measuredSourceWindows hα hτ hξ a D bits B C fixed F H small alphaCap hD G K hG hK
    growth fan] with n charge
  intro r R V z w p d k u o b entries cells bundles core powers rectangle reader l m g t header M Z X P L geo source windows
    hr hR RM Vcap rows ZZ hz cellsN groups team groupCount dEq axes cw rw word hw hb emitted geom
  obtain ⟨wordCost,out⟩ := geometrySubarrays_le (k:=k) (u:=u) hw hb emitted
  have bound := nat_le_ceiling geom
  exact charge r R V z w (2^p+2^d) k u o b entries cells bundles core powers rectangle reader l m g t header
    hr hR RM Vcap rows ZZ hz cellsN groups team groupCount dEq axes cw rw word (wordCost.trans bound) (out.trans bound) geom

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
