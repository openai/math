import OAI.Geometry.Hirsch.Scheduler
import OAI.Geometry.Hirsch.Elimination

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

namespace Blocking

variable {Coord Row : Type} [Fintype Coord] (block : Blocking Coord Row)

theorem eqOn_of_coeff_eq {first last : Vec Coord} (row : Row) (hle : first ≤ last)
    (he : block.coeff row first = block.coeff row last) : EqOn first last (block.support row) := by
  rw [block.expand row first, block.expand row last] at he
  have hh := (Finset.sum_eq_sum_iff_of_le (fun idx _ =>
    mul_le_mul_of_nonneg_left (hle idx) (block.weight_nonneg row idx))).mp he
  exact fun idx hi => mul_left_cancel₀ (block.weight_pos hi).ne' (hh idx (Finset.mem_univ _))

theorem support_nonempty (row : Row) : (block.support row).Nonempty := by
  by_contra hn
  have he : block.coeff row 1 = block.coeff row 0 := block.local_eq row (fun idx hi => (hn ⟨idx, hi⟩).elim)
  simp [(block.positive row).ne'] at he

theorem strict_pos (row : Row) {vec : Vec Coord} (hp : ∀ idx, 0 < vec idx) :
    0 < block.coeff row vec := by
  obtain ⟨idx, hi⟩ := block.support_nonempty row
  rw [block.expand]
  exact Finset.sum_pos' (fun other _ => mul_nonneg (block.weight_nonneg row other) (hp other).le)
    ⟨idx, Finset.mem_univ _, mul_pos (block.weight_pos hi) (hp idx)⟩

theorem support_bound [Finite Row] (hu : block.UnitWeights) (floor roof : ℝ) :
    ∃ bound, ∀ vec : Vec Coord, (∀ idx, floor ≤ vec idx) →
      ∀ row, block.coeff row vec ≤ roof → ∀ idx ∈ block.support row, vec idx ≤ bound := by
  obtain ⟨bound, hb⟩ := Finite.bddAbove_range
    (fun pair : Row × Coord => (roof - floor) / block.weight pair.1 pair.2 + floor)
  refine ⟨bound, fun vec hl row hr idx hi => le_trans ?_ (hb (mem_range_self (row, idx)))⟩
  let shifted := vec - fun _ => floor
  have he : block.coeff row shifted = block.coeff row vec - floor := by
    unfold shifted; rw [map_sub, hu.constant]
  have hh : block.weight row idx * (vec idx - floor) ≤ block.coeff row shifted := by
    rw [block.expand]
    exact Finset.single_le_sum (fun other _ =>
      mul_nonneg (block.weight_nonneg row other) (sub_nonneg.mpr (hl other))) (Finset.mem_univ idx)
  have ht : vec idx - floor ≤ (roof - floor) / block.weight row idx :=
    (le_div_iff₀ (block.weight_pos hi)).mpr (by linarith)
  linarith

end Blocking

namespace Coupler

variable {Coord Row Resource ResRow : Type} [Fintype Row] [Fintype Resource] [Finite ResRow]
  (cp : Coupler Coord Row Resource ResRow)

theorem slack_bound : ∃ bound > 0, ∀ vec slacks, (∀ side idx, 1 ≤ vec side idx) →
    cp.resPt vec slacks ∈ cp.res.system.body →
    (∀ idx, -bound ≤ slacks idx) ∧ ∀ row ∈ cp.res.system.active (cp.resPt vec slacks),
      ∀ idx ∈ cp.res.support row, slacks idx ≤ bound := by
  obtain ⟨bound, hb⟩ := cp.res.support_bound cp.resTune.unit (-1 - 2*cp.cap) 1
  refine ⟨max (1 + 2*cp.cap) bound, lt_of_lt_of_le (by linarith [cp.cap_ge]) (le_max_left ..), ?_⟩
  intro vec slacks hf hp
  have ht := cp.time_bound hf
  have hr : ∀ side, cp.read vec side ∈ Icc 0 cp.cap :=
    fun side => (cp.clockTune side).bound_mem (hf side) cp.cap_ge _ (abs_le.mp ht)
  have he : ∀ row, cp.rho * cp.res.slack row (cp.resPt vec slacks) =
      cp.res.coeff row slacks - cp.rho * (cp.res.slice (cp.time vec)).rhs row +
        (cp.read vec false + cp.read vec true) := by
    intro row
    rw [resPt, cp.resTune.slack, Tuned.line_some, sub_neg_eq_add]
  have hl : ∀ idx, -1 - 2*cp.cap ≤ slacks idx := by
    intro idx
    obtain ⟨row, hh⟩ := cp.resTune.unit.individual idx
    have hv := mul_nonneg cp.resTune.positive.le ((cp.res.feasible _).mp hp row)
    rw [he, hh, LinearMap.proj_apply] at hv
    linarith [(hr false).2, (hr true).2, (abs_le.mp (cp.resTune.rhs row _ ht)).1]
  refine ⟨fun idx => by linarith [hl idx, le_max_left (1 + 2*cp.cap) bound], ?_⟩
  intro row hh idx hi
  apply le_trans _ (le_max_right _ _)
  apply hb slacks hl row _ idx hi
  have hv := he row
  rw [(cp.res.tight _ _).mp hh, mul_zero] at hv
  linarith [(hr false).1, (hr true).1, (abs_le.mp (cp.resTune.rhs row _ ht)).2]

end Coupler

namespace Coloring

variable {pkg : Package} {client : Program} {buckets : ℕ}
  (paint : Coloring pkg client buckets) (bucket : Fin buckets)

instance (idx : client.Coord) : Nonempty (paint.group bucket idx) :=
  (show (paint.group bucket idx).Nonempty from paint.covered bucket idx).to_subtype

instance (idx : client.Coord) : Fintype (paint.group bucket idx) := Fintype.ofFinite _

def minimum (pt : Timed pkg.prog.Coord) (idx : client.Coord) :=
  least (fun row : paint.group bucket idx => pkg.block.slack row pt)

theorem minimum_le (pt : Timed pkg.prog.Coord) {idx row} (hr : row ∈ paint.group bucket idx) :
    paint.minimum bucket pt idx ≤ pkg.block.slack row pt :=
  least_le (fun src : paint.group bucket idx => pkg.block.slack src pt) ⟨row, hr⟩

theorem minimum_concave (first last : Timed pkg.prog.Coord) (idx : client.Coord) :
    (paint.minimum bucket first idx + paint.minimum bucket last idx) / 2 ≤
      paint.minimum bucket ((1/2 : ℝ) • (first + last)) idx := by
  apply least_concave
  intro row
  simp only [Blocking.slack, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    map_smul, map_add, smul_eq_mul]
  linarith

def Pick (coords : Set client.Coord) := (idx : coords) → paint.group bucket idx.val

instance (coords : Set client.Coord) : Fintype (paint.Pick bucket coords) := by
  classical
  unfold Pick
  infer_instance

def picked {coords : Set client.Coord} (pick : paint.Pick bucket coords) (idx : client.Coord) :
    paint.group bucket idx := by
  classical
  exact if hi : idx ∈ coords then pick ⟨idx, hi⟩ else Classical.arbitrary _

theorem minimizing (coords : Set client.Coord) (pt : Timed pkg.prog.Coord) :
    ∃ pick : paint.Pick bucket coords, ∀ idx ∈ coords,
      pkg.block.slack (paint.picked bucket pick idx) pt = paint.minimum bucket pt idx := by
  choose pick hp using fun idx => least_attained (fun row : paint.group bucket idx => pkg.block.slack row pt)
  refine ⟨fun idx => pick idx.val, fun idx hi => ?_⟩
  simpa [picked, hi, minimum] using (hp idx).symm

theorem card_pick (coords : Set client.Coord) {bound : ℕ}
    (hb : ∀ idx, (paint.group bucket idx).ncard ≤ bound) :
    Fintype.card (paint.Pick bucket coords) ≤ bound ^ coords.ncard := by
  classical
  unfold Pick
  rw [Fintype.card_pi]
  simpa only [fintypeCard_eq_ncard, Finset.prod_const, Finset.card_univ] using
    Finset.prod_le_prod (s := Finset.univ) (fun idx : coords => fun _ => hb idx)

end Coloring
end OAI.Geometry.Hirsch
