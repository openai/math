import OAI.Hierarchy.DescentChosenPhysicalLoads
import OAI.Hierarchy.DescentTetherNetwork

namespace OAI
/-! # The one-physical-bit reset selected by the harmonic account -/

namespace Hierarchy.DescentChosenRouter.Dyadic
open DescentColonies DescentRotor Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {V I H K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Field K]
variable {k n h bits C₀ d : ℕ} (D : Dyadic V I k) (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
variable {B factor unit : ℝ} (L : D.Loads (2^n) B (factor*B) unit)
variable (positive : 0<unit) (allowance : unit≤B) (power : 0<factor)
variable (available : (((2^n:ℕ):ℝ)^2)*bits≤factor)
variable (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures K G.arcs C₀ bits p)
variable (fallback : Bool→V×Block k→H)

include positive allowance power in
theorem unit_pos : 0<factor*(B/unit) := mul_pos power (div_pos (positive.trans_le allowance) positive)

include positive allowance in
theorem unit_fits : (1:ℝ)≤B/unit := (one_le_div positive).mpr allowance

include hw positive allowance available in
theorem unit_rows : ((2^n:ℕ):ℝ)*(B/unit)≤factor*(B/unit) := by
  have rows : (1:ℝ)≤(2^n:ℕ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.two_pow_pos n)
  have digit : (1:ℝ)≤bits := by exact_mod_cast hw
  have square : ((2^n:ℕ):ℝ)≤((2^n:ℕ):ℝ)^2 := by nlinarith
  have room : ((2^n:ℕ):ℝ)≤factor := square.trans ((le_mul_of_one_le_right (by positivity) digit).trans available)
  exact mul_le_mul_of_nonneg_right room (div_nonneg (positive.le.trans allowance) positive.le)

local notation "loads" => L.per_bit positive
local notation "paid" => (factor*(B/unit))
local notation "pos" => unit_pos positive allowance power
local notation "fit" => unit_fits positive allowance
local notation "rows" => unit_rows (n:=n) hw positive allowance available
local notation "placed" => D.install loads pos (by norm_num : (0:ℝ)<1) fit rows fallback
local notation "wt" => fun _ : I=>(1:ℕ)

def oneBitPlacement := placed

private def bitHardware : Hardware (K:=K) (C₀:=C₀) (u:=1) placed G hw paid := by
  let build (r : ℝ) := ∀ (book : D.Loads (2^n) (B/unit) paid r) (hp : 0<r) (fitBit : r≤B/unit),
    Hardware (K:=K) (C₀:=C₀) (u:=1) (D.install book pos hp fitBit rows fallback) G hw paid
  have castBit : build ((1:ℕ):ℝ) := fun book _ fitBit =>
    D.observed_hardware (u:=1) book pos (by decide) fitBit rows fallback G hw menu available
  have realBit : build 1 := (Nat.cast_one : ((1:ℕ):ℝ) = 1) ▸ castBit
  exact realBit loads (by norm_num) fit

local notation "hardware" => bitHardware D G hw L positive allowance power available menu fallback
local notation "devices" => selected (K:=K) (C₀:=C₀) (u:=1) placed G hw paid hardware
def configured := devices

/-- An actual trivalent network on the two groups of original one-bit
public rows. The scale of the integer accounting is absent from its wires. -/
def unit_reset := DescentMixedRouter.network (K:=K) (C₀:=C₀) G hw 1 (placed).contact (placed).input (placed).site
  (placed).owner (placed).align devices d

def unit_tables := DescentMixedRouter.coefficients (K:=K) (C₀:=C₀) G hw 1 (placed).contact (placed).input (placed).site
  (placed).owner (placed).align devices d

local notation "M" => unit_reset (d:=d) D G hw L positive allowance power available menu fallback
local notation "T" => unit_tables (d:=d) D G hw L positive allowance power available menu fallback

theorem reset_value (x : Ports (DescentRouterBank.publicWidth (placed).input wt)) :
    (M).value T x = if DescentRouterBank.publicRows (placed).input wt x false=
      DescentRouterBank.publicRows (placed).input wt x true then 1 else 0 :=
  DescentMixedRouter.value (K:=K) (C₀:=C₀) (D:=d) G hw 1 (placed).contact (placed).input
    (placed).site (placed).owner (placed).align devices x

theorem reset_degree (v : (M).Site) : (M).bitDegree v≤3 :=
  DescentMixedRouter.degree (K:=K) (C₀:=C₀) (D:=d) G hw 1 (placed).contact (placed).input
    (placed).site (placed).owner (placed).align devices v

/-- Multiplying the concrete physical gauge back by the unit charge reproduces
the paid dyadic base allowance when the corresponding device is chosen. -/
theorem good_price (s : Bool) (g : D.G) :
    unit*(devices s (.inl g)).goodBudget=factor*B :=
  restored_price positive

end
end Hierarchy.DescentChosenRouter.Dyadic

end OAI
