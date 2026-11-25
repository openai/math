import OAI.ThreeFlat.Diagonal.TickRuntimeBudget
import OAI.ThreeFlat.Diagonal.TickClockAllocation
import OAI.ThreeFlat.Diagonal.TraceVolumeArithmetic
import OAI.ThreeFlat.Diagonal.ApproximateImage

namespace OAI
/-! # Total fuel of the mounted tick at the paper's dyadic parameters -/

namespace ThreeFlat.Diagonal.TickTotalBudget

/-- Natural sizes and instruction counts consumed by the mounted native tick. -/
structure Charges where
  tickBits : ℕ
  teamBits : ℕ
  navigation : ℕ
  buckets : ℕ
  replay : ℕ
  selected : ℕ
  prepare : ℕ
  suffix : ℕ
  hidden : ℕ
  cells : ℕ
  entries : ℕ
  field : ℕ

def Charges.lookup (v : Charges) := 4+8*v.entries*(6*(8*v.entries)+10)
def Charges.fieldCost (v : Charges) := (v.field*v.field)*(6*(v.field*v.field)+10)

/-- Public front, navigation, request generator and the longer of scan and evaluation. -/
def Charges.fuel (v : Charges) (a : ℕ) :=
  159+6*(v.tickBits+v.teamBits)+25+18*a+
    (1470+v.navigation+21+
      ((14+a*5082)+(17+6*a+max (30+20*v.buckets+4319*a)
        (v.prepare+(53+v.fieldCost+5*v.hidden+550*v.cells)))))

/-- The replay majorant applies to the short public identifiers, bucket descriptors,
navigation and unexpanded preparation. Selected expansion and fixed padding have
their own numerical ceilings. -/
structure Bounds (v : Charges) (m x : ℕ) : Prop where
  identifiers : v.tickBits+v.teamBits ≤ x
  buckets : v.buckets ≤ x
  navigation : v.navigation ≤ x
  replay : v.replay ≤ x
  selected : v.selected ≤ m/4
  prepare : v.prepare ≤ v.replay+v.selected+v.lookup+(5+62*v.suffix)
  suffix : v.suffix ≤ 4*(2*(m/40000))
  hidden : v.hidden ≤ m/40000
  cells : v.cells ≤ 2*(m/40000)

/-- The scan branch has fixed overhead 1736 and costs 9425 per chunk bit.
Charging both navigation and unexpanded preparation gives the factor 28 on
the common history-size majorant. -/
theorem fuel_le {v : Charges} {a m x : ℕ} (b : Bounds v m x) (nonempty : 1 ≤ a)
    (admin : 11161*a+28*x ≤ m/4) (rom : 8*(64+v.lookup+v.fieldCost) ≤ m) :
    v.fuel a ≤ m := by
  have fixed : v.lookup+(5+62*v.suffix)+
      (53+v.fieldCost+5*(m/40000)+550*(2*(m/40000))) ≤ m/4 :=
    TickRuntimeBudget.fixed_ROM_quarter (entries := v.entries) (field := v.field)
      (by simpa only [Charges.lookup,Charges.fieldCost,Nat.add_assoc] using rom) b.suffix
  obtain ⟨ids,buckets,nav,replay,selected,prep,suffix,hidden,cells⟩ := b
  unfold Charges.fuel
  omega

def chunk (u : ℕ) := 2^(u^10-u^4)
def ageClock (u cm : ℕ) := 2^(u^10)/u^cm
/-- An entire navigation pass initializes the physical map of one word per chunk bit.
The same allowance also bounds public identifiers, unexpanded replay and bucket scans. -/
def replayBound (u e C : ℕ) := C*u^e*chunk u

/-- A short tree-replay estimate also fits the shared administrative clock. -/
theorem tree_replay_le {u : ℕ} (age : 8≤u) (e C : ℕ) :
    C*u^e*2^((7*u^10+9)/10) ≤ replayBound u e C :=
  Nat.mul_le_mul_left (C*u^e) (TickRuntimeBudget.replay_le_chunk age)

/-- A single explicit coefficient also covers the fixed field and template-library ROM. -/
def coefficient (v : Charges) (C : ℕ) := max (11161+28*C) (8*(64+v.lookup+v.fieldCost))

private theorem administrative {v : Charges} {u e C : ℕ} (age : 8 ≤ u) :
    11161*chunk u+28*replayBound u e C ≤ coefficient v C*u^e*chunk u := by
  have ep : 1 ≤ u^e := Nat.pow_pos (by omega)
  have rep : replayBound u e C = C*u^e*chunk u := rfl
  have chunkmul : chunk u ≤ u^e*chunk u := by
    simpa only [one_mul] using Nat.mul_le_mul_right (chunk u) ep
  have major : 11161+28*C ≤ coefficient v C := le_max_left ..
  calc
    11161*chunk u+28*replayBound u e C ≤ 11161*(u^e*chunk u)+28*(C*u^e*chunk u) := by omega
    _ = (11161+28*C)*u^e*chunk u := by ring
    _ ≤ coefficient v C*u^e*chunk u :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ major)

private theorem fixed_le_product {v : Charges} {u e C : ℕ} (hp : 1 ≤ u) :
    8*(64+v.lookup+v.fieldCost) ≤ coefficient v C*u^e*chunk u := by
  have ep : 1 ≤ u^e := Nat.pow_pos hp
  have ap : 1 ≤ chunk u := Nat.two_pow_pos _
  calc
    _ ≤ coefficient v C := le_max_right ..
    _ ≤ coefficient v C*u^e := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (coefficient v C) ep
    _ ≤ coefficient v C*u^e*chunk u := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (coefficient v C*u^e) ap

/-- At sufficiently large age the complete mounted program fits the team clock
for every pointer layout whose component counts meet the indicated ceilings. -/
theorem paper_scale {v : Charges} {u e cm C : ℕ} (age : 8 ≤ u)
    (constant : 4*coefficient v C ≤ u) (exponent : e+1+cm ≤ u)
    (bounds : Bounds v (ageClock u cm) (replayBound u e C)) :
    v.fuel (chunk u) ≤ ageClock u cm := by
  have hp : 1 ≤ u := by omega
  have quarter : coefficient v C*u^e*chunk u ≤ ageClock u cm/4 :=
    TickRuntimeBudget.chunk_quarter constant exponent hp
  have fixed := (fixed_le_product (v := v) (e := e) (C := C) hp).trans quarter
  exact fuel_le bounds (Nat.two_pow_pos _) ((administrative age).trans quarter) (by omega)

private theorem shared_admin {ids nav buckets replay a x : ℕ} (ha : 1 ≤ a) (hi : ids ≤ x)
    (hn : nav ≤ x) (hb : buckets ≤ x) (hr : replay ≤ x) :
    (1706+6*ids+nav+5106*a)+(30+20*buckets+4319*a)+replay ≤ 11161*a+28*x := by omega

private theorem terminal_eighth {m lut field suffix hidden cells : ℕ}
    (rom : 32*(64+lut+field) ≤ m) (s : suffix ≤ 4*(2*(m/40000)))
    (h : hidden ≤ m/40000) (j : cells ≤ 2*(m/40000)) :
    lut+(5+62*suffix)+(53+field+5*hidden+550*cells) ≤ m/8 := by
  have cap := Nat.div_mul_le_self m 40000
  calc
    _ ≤ (64+lut+field)+1601*(m/40000) := by omega
    _ ≤ m/8 := by omega

private theorem join_branches {base scan eval replay selected fixed m : ℕ}
    (admin : base+scan+replay ≤ m/8) (weights : eval ≤ replay+selected+fixed)
    (choice : selected ≤ m/4) (tail : fixed ≤ m/8) : base+max scan eval ≤ m/2 := by
  rcases le_total scan eval with h|h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega

/-- The variable part of the terminal ROM costs at most 1601 instructions per
unit of hidden capacity. The remaining constant terms fit into one thirty-second. -/
private theorem fuel_half_extra {v : Charges} {a m x extra : ℕ} (b : Bounds v m x) (nonempty : 1 ≤ a)
    (admin : extra+(11161*a+28*x) ≤ m/8) (rom : 32*(64+v.lookup+v.fieldCost) ≤ m) :
    extra+v.fuel a ≤ m/2 := by
  let base := 1706+6*(v.tickBits+v.teamBits)+v.navigation+5106*a
  let scan := 30+20*v.buckets+4319*a
  let terminal := 53+v.fieldCost+5*v.hidden+550*v.cells
  have normalized : extra+v.fuel a = (extra+base)+max scan (v.prepare+terminal) := by
    dsimp only [Charges.fuel,base,scan,terminal]
    ring
  rw [normalized]
  apply join_branches (replay := v.replay) (selected := v.selected)
    (fixed := v.lookup+(5+62*v.suffix)+terminal)
  · have work : base+scan+v.replay ≤ 11161*a+28*x :=
      shared_admin nonempty b.identifiers b.navigation b.buckets b.replay
    exact (by simpa only [Nat.add_assoc] using Nat.add_le_add_left work extra :
      extra+base+scan+v.replay ≤ extra+(11161*a+28*x)).trans admin
  · simpa only [Nat.add_assoc] using Nat.add_le_add_right b.prepare terminal
  · exact b.selected
  · exact terminal_eighth rom b.suffix b.hidden b.cells

theorem fuel_half {v : Charges} {a m x : ℕ} (b : Bounds v m x) (nonempty : 1 ≤ a)
    (admin : 11161*a+28*x ≤ m/8) (rom : 32*(64+v.lookup+v.fieldCost) ≤ m) :
    v.fuel a ≤ m/2 := by
  simpa only [Nat.zero_add] using fuel_half_extra (extra := 0) b nonempty (by simpa using admin) rom

/-- Increasing the age threshold by a factor of two places the tick in half
the team clock, as required by a power-of-two trace length. -/
theorem paper_half {v : Charges} {u e cm C : ℕ} (age : 8 ≤ u)
    (constant : 8*coefficient v C ≤ u) (exponent : e+1+cm ≤ u)
    (bounds : Bounds v (ageClock u cm) (replayBound u e C)) :
    v.fuel (chunk u) ≤ ageClock u cm/2 := by
  have hp : 1 ≤ u := by omega
  have quarter : (2*coefficient v C)*u^e*chunk u ≤ ageClock u cm/4 :=
    TickRuntimeBudget.chunk_quarter (by omega) exponent hp
  have twice : 2*(coefficient v C*u^e*chunk u) ≤ ageClock u cm/4 := by
    simpa only [Nat.mul_assoc] using quarter
  have eighth : coefficient v C*u^e*chunk u ≤ ageClock u cm/8 := by omega
  have fixed := (fixed_le_product (v := v) (e := e) (C := C) hp).trans eighth
  exact fuel_half bounds (Nat.two_pow_pos _) ((administrative age).trans eighth) (by omega)

/-- The rounded trace grid has enough sites for the complete mounted machine. -/
theorem trace_fuel {v : Charges} {u e C : ℕ} (age : 8 ≤ u)
    (constant : 8*coefficient v C ≤ u) (exponent : e+1+TraceVolume.cm ≤ u)
    (bounds : Bounds v (TraceVolume.cap u) (replayBound u e C)) :
    v.fuel (chunk u) ≤ 2^(TraceVolume.depth u) := by
  have half : v.fuel (chunk u) ≤ TraceVolume.cap u/2 := paper_half age constant exponent bounds
  have sites := (TraceVolume.sites_cap (u := u) (by omega)).2
  omega

def shift (v : Charges) (u np : ℕ) :=
  28+16*ApproximateImage.pinCount (2^(u^3)) v.tickBits v.teamBits np (chunk u)

private theorem public_le_chunk {u : ℕ} (age : 8 ≤ u) : 2^(u^3) ≤ chunk u := by
  have pos : 0 < u := by omega
  have p34 := Nat.pow_le_pow_right pos (by decide : 3 ≤ 4)
  have p45 : 2*u^4 ≤ u^5 := by
    rw [pow_succ u 4,Nat.mul_comm 2 (u^4)]
    exact Nat.mul_le_mul_left _ (by omega)
  have p510 := Nat.pow_le_pow_right pos (by decide : 5 ≤ 10)
  exact Nat.pow_le_pow_right (by decide) (by omega)

private theorem shift_le {v : Charges} {u e np : ℕ} (age : 8 ≤ u)
    (ids : v.tickBits+v.teamBits+np ≤ u^e) : shift v u np ≤ 124*(u^e*chunk u) := by
  have ep : 1 ≤ u^e := Nat.pow_pos (by omega)
  have ap : 1 ≤ chunk u := Nat.two_pow_pos _
  have a : chunk u ≤ u^e*chunk u := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (chunk u) ep
  have poly : u^e ≤ u^e*chunk u := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (u^e) ap
  have small := public_le_chunk age
  unfold shift ApproximateImage.pinCount
  omega

/-- Shifting the base-zero raw header costs 28 steps plus 16 per public pin.
The same physical evaluator and padding fit into the half-clock. -/
theorem shifted_paper_half {v : Charges} {u e cm C np : ℕ} (age : 8 ≤ u)
    (constant : 8*(coefficient v C+124) ≤ u) (exponent : e+1+cm ≤ u)
    (bounds : Bounds v (ageClock u cm) (replayBound u e C))
    (ids : v.tickBits+v.teamBits+np ≤ u^e) :
    shift v u np+v.fuel (chunk u) ≤ ageClock u cm/2 := by
  have hp : 1 ≤ u := by omega
  have quarter : (2*(coefficient v C+124))*u^e*chunk u ≤ ageClock u cm/4 :=
    TickRuntimeBudget.chunk_quarter (C := 2*(coefficient v C+124))
      (by simpa only [← Nat.mul_assoc] using constant) exponent hp
  have two : 2*((coefficient v C+124)*u^e*chunk u) ≤ ageClock u cm/4 := by
    simpa only [Nat.mul_assoc] using quarter
  have eighth : (coefficient v C+124)*u^e*chunk u ≤ ageClock u cm/8 := by omega
  have add : (coefficient v C+124)*u^e*chunk u = coefficient v C*u^e*chunk u+124*(u^e*chunk u) := by ring
  rw [add] at eighth
  have fixed := fixed_le_product (v := v) (e := e) (C := C) hp
  apply fuel_half_extra (a := chunk u) bounds (Nat.two_pow_pos _) _ (by omega)
  have front := shift_le age ids
  have main := administrative (v := v) (e := e) (C := C) age
  omega

theorem shifted_trace_fuel {v : Charges} {u e C np : ℕ} (age : 8 ≤ u)
    (constant : 8*(coefficient v C+124) ≤ u) (exponent : e+1+TraceVolume.cm ≤ u)
    (bounds : Bounds v (TraceVolume.cap u) (replayBound u e C))
    (ids : v.tickBits+v.teamBits+np ≤ u^e) :
    shift v u np+v.fuel (chunk u) ≤ 2^(TraceVolume.depth u) := by
  have half : shift v u np+v.fuel (chunk u) ≤ TraceVolume.cap u/2 :=
    shifted_paper_half age constant exponent bounds ids
  have sites := (TraceVolume.sites_cap (u := u) (by omega)).2
  omega

/-- The chronological seven-phase allocation and the complete mounted tick's
instruction bound hold simultaneously at the same dyadic age. -/
theorem paper_clock {v : Charges} {u e cm C groups chunks : ℕ} (age : 8 ≤ u)
    (constant : 4*coefficient v C ≤ u) (exponent : e+1+cm ≤ u)
    (bounds : Bounds v (ageClock u cm) (replayBound u e C))
    (dyadic : ∃ j : ℕ, groups = 2^j) (limit : groups ≤ 2^(2*u^4))
    (positive : 0 < chunks) (enough : chunks ≤ groups) :
    let T := 2^(u^6)
    let E := T/(4*groups)
    0 < groups ∧ chunks+2 ≤ E ∧ T = 4*(groups*E) ∧ v.fuel (chunk u) ≤ ageClock u cm := by
  have clock := TickChronology.clock_budget (w := u) (by omega) dyadic limit positive enough
  exact ⟨clock.1,clock.2.1,clock.2.2,paper_scale age constant exponent bounds⟩

/-- The same exponent covers the physical H gate/slot leaf bound and the native
selected-subtree tariff. It is fixed before choosing the H fuel saving or fold length. -/
def unitExponent : ℕ := 160

/-- Constant template tables, bounded geometry and the word-width loops of the
selected stage compiler may contribute a fixed multiplier depending on the block.
At a later age that constant and six native word-width factors fit into degree 61. -/
theorem unit_native_tariff {u B work : ℕ} (age : 1≤u) (constant : B*17^6≤u)
    (native : work≤B*(16*u^10+1)^6) : work≤u^61 := by
  have positive : 1≤u^10 := Nat.pow_pos age
  have head : 16*u^10+1≤17*u^10 := by omega
  calc
    work ≤ B*(16*u^10+1)^6 := native
    _ ≤ B*(17*u^10)^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left head _)
    _ = (B*17^6)*u^60 := by ring
    _ ≤ u^61 := by
      rw [pow_succ u 60,Nat.mul_comm (u^60) u]
      exact Nat.mul_le_mul_right _ constant

theorem unit_work {u B work : ℕ} (age : 1≤u) (constant : B*17^6≤u)
    (native : work≤B*(16*u^10+1)^6) : work≤u^unitExponent :=
  (unit_native_tariff age constant native).trans (Nat.pow_le_pow_right age (by decide))

/-- The degree loss in the total selected work of the physical block is an absolute
number. Increasing the fold-length exponent changes neither this value nor the tariff. -/
theorem unit_loss : 146+2*unitExponent+26=492 := rfl

end ThreeFlat.Diagonal.TickTotalBudget

end OAI
