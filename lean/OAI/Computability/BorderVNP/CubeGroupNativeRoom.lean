import OAI.Computability.BorderVNP.CubeGroupWeightPhysicalSchedule
import OAI.Computability.BorderVNP.CubeGroupChargeBounds
import OAI.Computability.BorderVNP.CubeGroupPhysicalRows
import OAI.Computability.BorderVNP.CubeSharedRowsCharge

/-! # The one-epoch team bound on the native output array

Equation (8.1) bounds the total shared widths. A fixed packet has a bounded
ratio of shared to raw width, and the balanced cell labels bound all incoming
data for each symbol. Together these give the constants on page 30 for every
word written by the verified team assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical VPVNP VPVNP.MotifBase Finset

variable {l : Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
variable {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups}
variable {A : Type*} [Fintype A] {label : Fin l.cells → Label (n+1) l.groups}
variable {recv : A → Fin l.cells} {w : A → ℕ}

/-- The total physical load in rational word units, using the exact lengths
in a passing declaration. -/
theorem sum_jointCost_le (s : ℕ) (select : Packet n l.groups blocks → Selector n K h)
    (pass : passesLengths b s select D) :
    (∑ u, jointCost blocks b K h D label recv w u) ≤
      2*(cutWidth b s select (chosen b s select) +
        Fintype.card (Packet n l.groups blocks)*MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℕ) +
      (∑ a, w a : ℕ) + 2*(padded n l.groups blocks (h*b) : ℚ)/1000000 := by
  have raw : ((∑ u : Fin l.groups, groupRaw (blocks*(h*b)) D.1 u : ℕ) : ℚ) ≤
      2*(padded n l.groups blocks (h*b) : ℚ) := by
    unfold padded
    exact_mod_cast SharedRows.sum_groupRaw_le (d := l.groups) (blocks*(h*b)) D.1
  have eq : (∑ u, jointCost blocks b K h D label recv w u) =
      ((∑ u, incidentWidth blocks K h D u : ℕ) : ℚ) + (∑ u, incomingWidth label recv w D.1 u : ℕ) +
        ((∑ u : Fin l.groups, groupRaw (blocks*(h*b)) D.1 u : ℕ) : ℚ)/1000000 := by
    simp [jointCost,sum_add_distrib,sum_div]
  rw [eq,sum_incidentWidth b s select D pass,sum_incomingWidth]
  push_cast
  have h := div_le_div_of_nonneg_right raw (by norm_num : (0 : ℚ) ≤ 1000000)
  push_cast at h
  linarith only [h]

/-- The verified physical cut of this declaration bounds the total group load. -/
theorem sum_jointCost_le_cut (s : ℕ) (select : Packet n l.groups blocks → Selector n K h)
    (pass : passesLengths b s select D) (volume : ℕ) (η : ℝ)
    (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (dir : (cutWidth b s select (chosen b s select) : ℝ) +
      ∑ _p : Packet n l.groups blocks, (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤
      padded n l.groups blocks (h*b) * (2/Real.sqrt (n+1)+(n+1)/l.groups+η))
    (groupRoom : (n+1 : ℝ)/l.groups ≤ 1/10^6)
    (paddingRoom : padded n l.groups blocks (h*b) ≤ 5*volume)
    (dataRoom : 4096*(∑ a, w a) ≤ volume) :
    (∑ u, jointCost blocks b K h D label recv w u) ≤ (volume : ℚ)/1024 := by
  let W : ℝ := volume
  let P : ℝ := padded n l.groups blocks (h*b)
  have posW : 0 ≤ W := by dsimp [W]; positivity
  have hP : P ≤ 5*W := by dsimp only [P,W]; exact_mod_cast paddingRoom
  have hdata : ((∑ a, w a : ℕ) : ℝ) ≤ W/4096 := by
    have := Nat.cast_le (α := ℝ).mpr dataRoom
    dsimp only [W]
    push_cast at this ⊢
    linarith
  simp only [sum_const,card_univ,nsmul_eq_mul] at dir
  have rate : 2/Real.sqrt (n+1)+(n+1)/l.groups+η ≤ (2 : ℝ)/10^6 := by linarith
  have dtotal : ((cutWidth b s select (chosen b s select) +
        Fintype.card (Packet n l.groups blocks)*MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℕ) : ℝ) ≤
      (5*W)*((2 : ℝ)/10^6) := by
    push_cast
    exact dir.trans ((mul_le_mul_of_nonneg_left rate (show 0 ≤ P by dsimp [P]; positivity)).trans
      (mul_le_mul_of_nonneg_right hP (by norm_num)))
  apply Rat.cast_le (K := ℝ) |>.mp
  have he := Rat.cast_le (K := ℝ) |>.mpr (sum_jointCost_le (label := label) (recv := recv) (w := w) s select pass)
  push_cast at he dtotal ⊢
  dsimp only [P,W] at hdata hP posW dtotal
  push_cast at hdata
  linarith only [he,hdata,hP,posW,dtotal]

/-- The aggregate bound only depends on the verified row declaration and physical
widths, so it can be established before allocating or running the team passes. -/
theorem sum_jointCost_le_volume (s : ℕ) (select : Packet n l.groups blocks → Selector n K h)
    (pass : passesLengths b s select D) (volume : ℕ) (hd : 0 < l.groups) (η : ℝ) (hη : 0 ≤ η)
    (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (width : ∀ σ : Fin h → Edge (n+1), (∑ e, (payload (onEdge s) σ e : ℝ)) ≤
      2*2^n*Real.sqrt (n+1)*(h*b : ℕ))
    (selector : (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤ η*(h*b : ℕ))
    (groupRoom : (n+1 : ℝ)/l.groups ≤ 1/10^6)
    (paddingRoom : padded n l.groups blocks (h*b) ≤ 5*volume)
    (dataRoom : 4096*(∑ a, w a) ≤ volume) :
    (∑ u, jointCost blocks b K h D label recv w u) ≤ (volume : ℚ)/1024 :=
  sum_jointCost_le_cut s select pass volume η fixed (chosen_coordinate_budget b s select hd hη width selector)
    groupRoom paddingRoom dataRoom

/-- One symbol's incident, delivered and padded widths fit a single team
charge before any native schedule has been executed. -/
theorem jointCost_le_symbol_budget (s : ℕ)
    (select : Packet n l.groups blocks → Selector n K h) (pass : passesLengths b s select D)
    (X R M : ℕ) (hM : 1 ≤ M) (hd : 0 < l.groups)
    (packet : h*s + MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h ≤ M*(2^n*(h*b)))
    (balanced : ∀ u, Balancing.load (Balancing.datum (fun j : Balancing.Bits w => recv j.1) u) label ≤
      4*((X*(R+1) : ℕ) : ℝ)/((l.groups^(n+1) : ℕ) : ℝ))
    (localRoom : 1024*(10*(M+1)+4)*(R+1) ≤ l.groups)
    (paddingRoom : padded n l.groups blocks (h*b) ≤ 5*(X*(R+1)))
    (u : Fin l.groups) : jointCost blocks b K h D label recv w u ≤ (X : ℚ)/1024 := by
  let W : ℝ := (X*(R+1) : ℕ)
  let P : ℝ := padded n l.groups blocks (h*b)
  have hP : P ≤ 5*W := by dsimp only [P,W]; exact_mod_cast paddingRoom
  apply Rat.cast_le (K := ℝ) |>.mp
  have hd' : 0 < (l.groups : ℝ) := by exact_mod_cast hd
  have hr : (groupRaw (blocks*(h*b)) D.1 u : ℝ) ≤ 2*P/l.groups := by
    apply (le_div_iff₀ hd').mpr
    dsimp only [P,padded]
    exact_mod_cast groupRaw_le (blocks*(h*b)) D.1 u
  have hi : (incidentWidth blocks K h D u : ℝ) ≤ M*(groupRaw (blocks*(h*b)) D.1 u : ℝ) := by
    exact_mod_cast incidentWidth_le_raw b s select D pass u M hM packet
  have hinc := incomingWidth_le label recv w D.1 u W balanced
  have raw : (groupRaw (blocks*(h*b)) D.1 u : ℝ) ≤ 10*W/l.groups := hr.trans
    (div_le_div_of_nonneg_right (by linarith) hd'.le)
  have rough := mul_le_mul_of_nonneg_left raw (show (0 : ℝ) ≤ M by positivity)
  have charge : (jointCost blocks b K h D label recv w u : ℝ) ≤ (10*(M+1)+4)*W/l.groups := by
    rw [jointCost]
    push_cast
    have hrpos : 0 ≤ (groupRaw (blocks*(h*b)) D.1 u : ℝ) := by positivity
    calc
      _ ≤ M*(10*W/l.groups) + 4*W/l.groups + 10*W/l.groups := by
        linarith only [hi,hinc,rough,raw,hrpos]
      _ = _ := by ring
  have cap : (10*(M+1)+4)*W/l.groups ≤ (X : ℝ)/1024 := by
    apply (div_le_iff₀ hd').mpr
    have room : 1024*(10*((M : ℝ)+1)+4)*(R+1) ≤ l.groups := by exact_mod_cast localRoom
    have := mul_le_mul_of_nonneg_left room (show (0 : ℝ) ≤ X by positivity)
    dsimp only [W]; push_cast
    nlinarith only [this]
  push_cast
  exact charge.trans cap

/-- The native schedule at the verified cut fits the total and per-team exterior budgets. -/
theorem ScheduleResult.team_le_exterior_of_cut (result : ScheduleResult l teams orig mem)
    (image : PhysicalImage l orig blocks b K h D label recv w)
    (s : ℕ) (select : Packet n l.groups blocks → Selector n K h) (pass : passesLengths b s select D)
    (X M : ℕ) (hM : 1 ≤ M) (hd : 0 < l.groups) (η : ℝ)
    (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (packet : h*s + MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h ≤ M*(2^n*(h*b)))
    (dir : (cutWidth b s select (chosen b s select) : ℝ) +
      ∑ _p : Packet n l.groups blocks, (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤
      padded n l.groups blocks (h*b) * (2/Real.sqrt (n+1)+(n+1)/l.groups+η))
    (balanced : ∀ u, Balancing.load (Balancing.datum (fun j : Balancing.Bits w => recv j.1) u) label ≤
      4*((X*(teams.r+1) : ℕ) : ℝ)/((l.groups^(n+1) : ℕ) : ℝ))
    (groupRoom : (n+1 : ℝ)/l.groups ≤ 1/10^6)
    (localRoom : 1024*(10*(M+1)+4)*(teams.r+1) ≤ l.groups)
    (paddingRoom : padded n l.groups blocks (h*b) ≤ 5*(X*(teams.r+1)))
    (dataRoom : 4096*(∑ a, w a) ≤ X*(teams.r+1)) :
    (∑ u, jointCost blocks b K h D label recv w u) ≤ ((X*(teams.r+1) : ℕ) : ℚ)/1024 ∧
      ∀ j : Fin (teams.r+1), TeamNative.unscale (mem (teams.totals+j.val)) ≤ (X : ℚ)/256 := by
  have total := sum_jointCost_le_cut (label := label) (recv := recv) s select pass
    (X*(teams.r+1)) η fixed dir groupRoom paddingRoom dataRoom
  refine ⟨total,fun j => ?_⟩
  have maxGroup := jointCost_le_symbol_budget s select pass X teams.r M hM hd packet balanced localRoom paddingRoom
  have team := result.team_physical_le image ((X : ℚ)/1024) (by positivity) maxGroup j
  have hR : 0 < (teams.r : ℚ)+1 := by positivity
  have mean : (∑ u, jointCost blocks b K h D label recv w u)/(teams.r+1) ≤ (X : ℚ)/1024 := by
    apply (div_le_iff₀ hR).mpr
    push_cast at total
    linarith only [total]
  linarith only [team,mean,show (0 : ℚ) ≤ X by positivity]

/-- From the actual packet identity estimates and the balancing and padding
budgets, all native group words together use at most `X₀R/1024` units. Each
native team word uses at most `X₀/256` units. -/
theorem ScheduleResult.team_le_exterior (result : ScheduleResult l teams orig mem)
    (image : PhysicalImage l orig blocks b K h D label recv w)
    (s : ℕ) (select : Packet n l.groups blocks → Selector n K h) (pass : passesLengths b s select D)
    (X M : ℕ) (hM : 1 ≤ M) (hd : 0 < l.groups) (η : ℝ) (hη : 0 ≤ η)
    (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (packet : h*s + MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h ≤ M*(2^n*(h*b)))
    (width : ∀ σ : Fin h → Edge (n+1), (∑ e, (payload (onEdge s) σ e : ℝ)) ≤
      2*2^n*Real.sqrt (n+1)*(h*b : ℕ))
    (selector : (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤ η*(h*b : ℕ))
    (balanced : ∀ u, Balancing.load (Balancing.datum (fun j : Balancing.Bits w => recv j.1) u) label ≤
      4*((X*(teams.r+1) : ℕ) : ℝ)/((l.groups^(n+1) : ℕ) : ℝ))
    (groupRoom : (n+1 : ℝ)/l.groups ≤ 1/10^6)
    (localRoom : 1024*(10*(M+1)+4)*(teams.r+1) ≤ l.groups)
    (paddingRoom : padded n l.groups blocks (h*b) ≤ 5*(X*(teams.r+1)))
    (dataRoom : 4096*(∑ a, w a) ≤ X*(teams.r+1)) :
    (∑ u, jointCost blocks b K h D label recv w u) ≤ ((X*(teams.r+1) : ℕ) : ℚ)/1024 ∧
      ∀ j : Fin (teams.r+1), TeamNative.unscale (mem (teams.totals+j.val)) ≤ (X : ℚ)/256 :=
  result.team_le_exterior_of_cut image s select pass X M hM hd η fixed packet
    (chosen_coordinate_budget b s select hd hη width selector) balanced groupRoom localRoom paddingRoom dataRoom

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
