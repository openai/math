import OAI.Computability.BorderVNP.RoutingCapacity
import OAI.Computability.BorderVNP.TransmissionScheduled

/-! # Capacity of the two-hop schedule of the actual descriptor table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open Finset Filter VPVNP.BurstRAM

/-- Bit width charged to this team's exterior budget by one descriptor. A
co-located pair is processed locally, and hence has zero exterior width. -/
def TableRow.exteriorWidth (r : TableRow) (u : ℕ) : ℕ :=
  if r.first ≠ r.second ∧ (r.first = u ∨ r.second = u) then r.width else 0

private theorem index_injective {R a b c d : ℕ} (hb : b < R) (hd : d < R)
    (h : a*R+b = c*R+d) : a = c ∧ b = d := by
  have smaller {x y p q : ℕ} (hxy : x < y) (hp : p < R) : x*R+p < y*R+q := by
    have h := Nat.mul_le_mul_right R (Nat.succ_le_of_lt hxy)
    rw [Nat.succ_mul] at h
    omega
  have eq : a = c := by
    rcases lt_trichotomy a c with hlt | eq | hgt
    · exact False.elim ((smaller (q := d) hlt hb).ne h)
    · exact eq
    · exact False.elim ((smaller (q := b) hgt hd).ne h.symm)
  subst c
  exact ⟨rfl,by omega⟩

/-- A valid row-major pair key identifies precisely one unordered pair. -/
theorem TableLayout.pairKey_eq_iff (l : TableLayout) {a b c d : ℕ}
    (ha : a < l.teams) (hb : b < l.teams) (hc : c < l.teams) (hd : d < l.teams) :
    l.pairKey a b = l.pairKey c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    obtain ⟨lo,hi⟩ := index_injective (max_lt ha hb) (max_lt hc hd) h
    change min a b = min c d at lo
    omega
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · simp only [TableLayout.pairKey, min_comm, max_comm]

private theorem demand_rows (l : TableLayout) (row : ℕ → TableRow)
    (labels : ∀ i < l.count, (row i).first < l.teams ∧ (row i).second < l.teams) (u v : Fin l.teams) :
    Routing.demand (l.widthMatrix row) u v = ∑ i ∈ range l.count,
      if (row i).first ≠ (row i).second ∧
        ((row i).first = u.val ∧ (row i).second = v.val ∨ (row i).first = v.val ∧ (row i).second = u.val)
      then (row i).width else 0 := by
  by_cases e : u = v
  · subst v
    rw [Routing.demand, ite_eq_left rfl]
    symm
    apply sum_eq_zero
    intro i _
    split
    next h => exact False.elim (h.1 ((h.2.elim id id).1.trans (h.2.elim id id).2.symm))
    next => rfl
  · have mono : Monotone (@Fin.val l.teams) := fun _ _ h => h
    simp only [Routing.demand, ite_eq_right e, TableLayout.widthMatrix, TableLayout.pairWidth,
      mono.map_min, mono.map_max]
    apply sum_congr rfl
    intro i hi
    obtain ⟨ha,hb⟩ := labels i (mem_range.mp hi)
    simp only [← show l.pairKey u.val v.val = min u.val v.val*l.teams+max u.val v.val from rfl,
      l.pairKey_eq_iff ha hb u.isLt v.isLt]

private theorem row_width_sum {R : ℕ} (r : TableRow) (u : Fin R) (ha : r.first < R) (hb : r.second < R) :
    (∑ v : Fin R, if r.first ≠ r.second ∧
      (r.first = u.val ∧ r.second = v.val ∨ r.first = v.val ∧ r.second = u.val)
      then r.width else 0) = r.exteriorWidth u := by
  by_cases eq : r.first = r.second
  · simp [eq, TableRow.exteriorWidth]
  simp only [TableRow.exteriorWidth, ne_eq, eq, not_false_eq_true, true_and]
  by_cases a : r.first = u.val
  · have b : r.second ≠ u.val := fun h => eq (a.trans h.symm)
    let t : Fin R := ⟨r.second,hb⟩
    have partner (v : Fin R) : r.second = v.val ↔ v = t :=
      ⟨fun e => Fin.ext e.symm,fun e => (congrArg Fin.val e).symm⟩
    simp [a, b, partner]
  · by_cases b : r.second = u.val
    · let t : Fin R := ⟨r.first,ha⟩
      have partner (v : Fin R) : r.first = v.val ↔ v = t :=
        ⟨fun e => Fin.ext e.symm,fun e => (congrArg Fin.val e).symm⟩
      simp [a, b, partner]
    · simp [a, b]

/-- Summing the table-driven demand over all partners counts every incident
nonlocal descriptor once, with its entire width, and counts local rows zero times. -/
theorem TableLayout.demand_sum_eq (l : TableLayout) (row : ℕ → TableRow)
    (labels : ∀ i < l.count, (row i).first < l.teams ∧ (row i).second < l.teams) (u : Fin l.teams) :
    ∑ v, Routing.demand (l.widthMatrix row) u v = ∑ i ∈ range l.count, (row i).exteriorWidth u := by
  simp_rw [demand_rows l row labels]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  exact row_width_sum _ _ (labels i (mem_range.mp hi)).1 (labels i (mem_range.mp hi)).2

/-- At the manuscript's rounded link scale, the actual per-team widths of the
descriptor table guarantee room for the common prefix and both directions of
every physical block. The threshold precedes the team count and table. -/
theorem eventually_table_leg_capacity {α ξ : ℝ} (hξ : 0 ≤ ξ) (gap : ξ+2*α < 1/25) :
    ∀ᶠ n : ℕ in atTop, ∀ (l : TableLayout) (row : ℕ → TableRow),
      (∀ i < l.count, (row i).first < l.teams ∧ (row i).second < l.teams) → ∀
      (hR : 2 < l.teams) (f : BroadcastFrame), 1 ≤ f.processors →
      (l.teams : ℝ) ≤ (n : ℝ) ^ (2*α) → (f.header : ℝ) ≤ f.processors * (n : ℝ) ^ (24/25 : ℝ) →
      f.link = TeamScales.link ξ l.teams n →
      (∀ u : Fin l.teams, ∑ i ∈ range l.count, (row i).exteriorWidth u ≤
        TeamScales.exterior ξ f.processors n / 64) →
      ∀ u v, f.header + Routing.legLoad hR (l.widthMatrix row) u v +
        Routing.legLoad hR (l.widthMatrix row) v u ≤ f.capacity := by
  filter_upwards [Routing.eventually_fit_block hξ gap] with n h
  intro l row labels hR f procs teams header link budget u v
  have widthBudget (x : Fin l.teams) := (l.demand_sum_eq row labels x).le.trans (budget x)
  simpa only [BroadcastFrame.capacity, link, Nat.mul_comm f.processors] using
    h f.processors l.teams f.header hR procs teams header (l.widthMatrix row) widthBudget u v

/-- At every sufficiently large length, the actual memory image supplies the endpoint
schedule, both addresses of the relay traversal, and the fitted span of every native
row. Only the descriptor widths enter the incident exterior budget. -/
theorem eventually_table_schedule {α ξ : ℝ} (hξ : 0 ≤ ξ) (gap : ξ+2*α < 1/25) :
    ∀ᶠ n : ℕ in atTop, ∀ (w : ℕ) (l : TableLayout) (row : ℕ → TableRow)
      (before : ℕ → ℕ) (pub : Arg → Word w) (m : Memory w) (f : BroadcastFrame)
      (teams : f.teams = l.teams),
      l.Image row before (readings m) → l.Allocated w → l.RowsFit w row → l.recordsMatch row before →
      (pub 0).val = l.frame → l.frameFields before → f.At (readings pub) (readings m) →
      f.Fits w (pub 0).val → (l.teams : ℝ) ≤ (n : ℝ) ^ (2*α) →
      (f.header : ℝ) ≤ f.processors * (n : ℝ) ^ (24/25 : ℝ) → f.link = TeamScales.link ξ l.teams n →
      (∀ u : Fin l.teams, ∑ i ∈ range l.count, (row i).exteriorWidth u ≤
        TeamScales.exterior ξ f.processors n / 64) →
      Transmission.Schedule f (Transmission.tableWidth l row teams) pub m ∧
      RelayRooms w l.teams (fun u y => l.partnerLength row u f.team y) (readings pub) (readings m) f.team ∧
      ∀ i < l.count, Transmission.ScheduledRange f (Transmission.tableWidth l row teams)
        (Transmission.tableRange l m i) := by
  filter_upwards [eventually_table_leg_capacity hξ gap] with n cap
  intro w l row before pub m f teams image al rowsFit initial hf loaded im fit scale head link budget
  have capacity := cap l row (fun i hi => (rowsFit.labels i hi).2) al.teamCount f fit.procs scale head link budget
  exact ⟨Transmission.Schedule.of_table image al pub hf loaded f im fit teams capacity,
    image.relayRooms al (readings pub) hf loaded f im fit capacity,
    fun _ hi => Transmission.ScheduledRange.of_table image al rowsFit initial f teams hi⟩

end RoutingISA

end BorderVNP
end Computability
end OAI
