import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

/-!
# Partitioning RAM calls by cumulative cost

In Lemma 10.1 of *VP and VNP differ over every field*, the site of a call is
determined by its starting cost. A call costs one plus its number of external
probes. The construction below preserves the full sequence of calls, so calls
with identical costs but different nondeterministic choices remain distinct.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMBuckets

variable {Call : Type*}

/-- Cost of a contiguous sequence of calls. -/
def cost (probes : Call → ℕ) : List Call → ℕ
  | [] => 0
  | a :: xs => (1 + probes a) + cost probes xs

@[simp] theorem cost_append (probes : Call → ℕ) (xs ys : List Call) :
    cost probes (xs ++ ys) = cost probes xs + cost probes ys := by
  induction xs with
  | nil => simp [cost]
  | cons a xs ih => simp [cost, ih, Nat.add_assoc]

@[simp] theorem cost_eq_zero_iff (probes : Call → ℕ) (xs : List Call) :
    cost probes xs = 0 ↔ xs = [] := by
  cases xs <;> simp [cost]

/-- All calls start before the boundary, including a last call that may finish
on or beyond the boundary. -/
def StartsBefore (probes : Call → ℕ) (boundary : ℕ) : ℕ → List Call → Prop
  | _, [] => True
  | start, a :: xs =>
    start < boundary ∧ StartsBefore probes boundary (start + (1 + probes a)) xs

/-- Split immediately before the first call that starts on or beyond the boundary. -/
def split (probes : Call → ℕ) (boundary : ℕ) : ℕ → List Call → List Call × List Call
  | _, [] => ([], [])
  | start, a :: xs =>
    if start < boundary then
      let rest := split probes boundary (start + (1 + probes a)) xs
      (a :: rest.1, rest.2)
    else ([], a :: xs)

/-- The site takes an initial segment. It can stop with work left only after
reaching its boundary. -/
structure IsSplit (probes : Call → ℕ) (boundary start : ℕ) (xs front rest : List Call) : Prop where
  append_eq : front ++ rest = xs
  before : StartsBefore probes boundary start front
  stopped : rest ≠ [] → boundary ≤ start + cost probes front

theorem split_spec (probes : Call → ℕ) (boundary start : ℕ) (xs : List Call) :
    IsSplit probes boundary start xs (split probes boundary start xs).1
      (split probes boundary start xs).2 := by
  induction xs generalizing start with
  | nil => exact ⟨rfl, trivial, by simp [split]⟩
  | cons a xs ih =>
    by_cases h : start < boundary
    · simp only [split, h, ↓reduceIte]
      have hr := ih (start + (1 + probes a))
      exact ⟨by simp [hr.append_eq], ⟨h, hr.before⟩,
        fun hn => by simpa [cost, Nat.add_assoc] using hr.stopped hn⟩
    · simp only [split, h, ↓reduceIte]
      exact ⟨rfl, trivial, fun _ => by simpa [cost] using Nat.le_of_not_gt h⟩

theorem IsSplit.eq_split {probes : Call → ℕ} {boundary start : ℕ} {xs front rest : List Call}
    (h : IsSplit probes boundary start xs front rest) :
    split probes boundary start xs = (front, rest) := by
  rcases h with ⟨rfl, hbefore, hstop⟩
  induction front generalizing start with
  | nil =>
    cases rest with
    | nil => rfl
    | cons a rest =>
      have hc := hstop (by simp)
      simp only [cost, Nat.add_zero] at hc
      simp [split, Nat.not_lt.mpr hc]
  | cons a front ih =>
    obtain ⟨hlt, htail⟩ := hbefore
    simp [split, hlt, ih htail (by simpa [cost, Nat.add_assoc] using hstop)]

/-- Starting with site `v`, run the successive start-cost cutoffs. Sites after a
halt receive empty lists. -/
def partition (probes : Call → ℕ) (H : ℕ) : ℕ → ℕ → ℕ → List Call → List (List Call)
  | _, 0, _, _ => []
  | v, sites + 1, start, xs =>
    let parts := split probes ((v + 1) * H) start xs
    parts.1 :: partition probes H (v + 1) sites (start + cost probes parts.1) parts.2

/-- The local cost checks on the successor chain. -/
def Valid (probes : Call → ℕ) (H : ℕ) : ℕ → ℕ → List (List Call) → Prop
  | _, _, [] => True
  | v, start, front :: blocks =>
    (front ≠ [] → v * H ≤ start) ∧
    StartsBefore probes ((v + 1) * H) start front ∧
    (blocks.flatten ≠ [] → (v + 1) * H ≤ start + cost probes front) ∧
    Valid probes H (v + 1) (start + cost probes front) blocks

@[simp] theorem length_partition (probes : Call → ℕ) (H v sites start : ℕ) (xs : List Call) :
    (partition probes H v sites start xs).length = sites := by
  induction sites generalizing v start xs with
  | zero => rfl
  | succ k ih => simp [partition, ih]

theorem partition_spec {probes : Call → ℕ} {H v sites start : ℕ} {xs : List Call}
    (hlower : xs ≠ [] → v * H ≤ start)
    (hcap : start + cost probes xs ≤ (v + sites) * H) :
    (partition probes H v sites start xs).flatten = xs ∧
      Valid probes H v start (partition probes H v sites start xs) := by
  induction sites generalizing v start xs with
  | zero =>
    have hempty : xs = [] := by
      by_contra hn
      have h := hlower hn
      have hp := (cost_eq_zero_iff probes xs).not.mpr hn
      simp only [Nat.add_zero] at hcap
      omega
    exact ⟨hempty.symm, trivial⟩
  | succ k ih =>
    let p := split probes ((v + 1) * H) start xs
    have hs : IsSplit probes ((v + 1) * H) start xs p.1 p.2 := split_spec ..
    have htotal : cost probes p.1 + cost probes p.2 = cost probes xs := by
      rw [← cost_append, hs.append_eq]
    obtain ⟨hflat, hvalid⟩ := ih (v := v + 1) (xs := p.2) hs.stopped (by
      rw [Nat.add_assoc, htotal]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap)
    refine ⟨?_, ?_⟩
    · change p.1 ++ (partition probes H (v + 1) k _ p.2).flatten = xs
      rw [hflat, hs.append_eq]
    · refine ⟨fun h => hlower ?_, hs.before, ?_, hvalid⟩
      · rw [← hs.append_eq]
        exact fun he => h (List.append_eq_nil_iff.mp he).1
      · change (partition probes H (v + 1) k _ p.2).flatten ≠ [] → _
        rw [hflat]
        exact hs.stopped

theorem Valid.eq_partition {probes : Call → ℕ} {H v start : ℕ} {blocks : List (List Call)}
    (h : Valid probes H v start blocks) :
    partition probes H v blocks.length start blocks.flatten = blocks := by
  induction blocks generalizing v start with
  | nil => rfl
  | cons front blocks ih =>
    obtain ⟨_, hbefore, hstop, htail⟩ := h
    have hs : IsSplit probes ((v + 1) * H) start (front ++ blocks.flatten) front blocks.flatten :=
      ⟨rfl, hbefore, hstop⟩
    simp [partition, hs.eq_split, ih htail]

/-- There is exactly one contiguous grouping into the given number of sites
that recovers the original path and passes the local start/stop cost checks. -/
theorem existsUnique_partition (probes : Call → ℕ) (S H : ℕ) (xs : List Call)
    (hcap : cost probes xs ≤ S * H) :
    ∃! blocks : List (List Call), blocks.length = S ∧ blocks.flatten = xs ∧
      Valid probes H 0 0 blocks := by
  have hs := partition_spec (v := 0) (start := 0) (sites := S) (xs := xs)
    (fun _ => by simp) (by simpa using hcap)
  refine ⟨partition probes H 0 S 0 xs, ⟨length_partition .., hs⟩, ?_⟩
  rintro blocks ⟨hlen, hxs, hv⟩
  simpa [hlen, hxs] using hv.eq_partition.symm

/-- Inspect the start cost of a specified call after a prefix of its block. -/
theorem StartsBefore.start_lt {probes : Call → ℕ} {boundary start : ℕ}
    {front rest : List Call} {a : Call}
    (h : StartsBefore probes boundary start (front ++ a :: rest)) :
    start + cost probes front < boundary := by
  induction front generalizing start with
  | nil => simpa [cost] using h.1
  | cons b front ih =>
    simpa [cost, Nat.add_assoc] using ih h.2

/-- Every call in a valid site block has exactly the site number prescribed by
the floor of its starting cost divided by the bucket size. -/
theorem call_site {probes : Call → ℕ} {H v start : ℕ} {front rest : List Call} {a : Call}
    (hH : 0 < H) (hlower : v * H ≤ start)
    (hb : StartsBefore probes ((v + 1) * H) start (front ++ a :: rest)) :
    (start + cost probes front) / H = v := by
  have hlo : v ≤ (start + cost probes front) / H :=
    (Nat.le_div_iff_mul_le hH).mpr (Nat.le_trans hlower (Nat.le_add_right ..))
  have hhi : (start + cost probes front) / H < v + 1 :=
    (Nat.div_lt_iff_lt_mul hH).mpr hb.start_lt
  omega

/-- A permitted call can only stay in its bucket or advance one bucket. -/
theorem next_bucket {H start charge : ℕ} (hH : 0 < H) (hc : charge ≤ H) :
    (start + charge) / H = start / H ∨ (start + charge) / H = start / H + 1 := by
  have hl : start / H ≤ (start + charge) / H := Nat.div_le_div_right (Nat.le_add_right ..)
  have hb : start < (start / H + 1) * H :=
    (Nat.div_lt_iff_lt_mul hH).mp (Nat.lt_succ_self _)
  have hu : (start + charge) / H < (start / H + 1 + 1) := by
    apply (Nat.div_lt_iff_lt_mul hH).mpr
    rw [Nat.succ_mul]
    omega
  omega

theorem StartsBefore.finish_lt {probes : Call → ℕ} {boundary H start : ℕ} {xs : List Call}
    (hb : StartsBefore probes boundary start xs) (hne : xs ≠ [])
    (hc : ∀ a ∈ xs, 1 + probes a ≤ H) :
    start + cost probes xs < boundary + H := by
  induction xs generalizing start with
  | nil => contradiction
  | cons a xs ih =>
    obtain ⟨hs, ht⟩ := hb
    have ha := hc a (by simp)
    by_cases he : xs = []
    · subst xs
      simp only [cost, Nat.add_zero]
      omega
    · simpa [cost, Nat.add_assoc] using ih ht he (fun b hm => hc b (by simp [hm]))

/-- The last call starts before the upper boundary and costs at most `H`. -/
theorem site_cost_lt {probes : Call → ℕ} {H v start : ℕ} {xs : List Call}
    (hH : 0 < H) (hlower : xs ≠ [] → v * H ≤ start)
    (hb : StartsBefore probes ((v + 1) * H) start xs)
    (hc : ∀ a ∈ xs, 1 + probes a ≤ H) :
    cost probes xs < 2 * H := by
  by_cases he : xs = []
  · simp [he, cost, hH]
  have hf := hb.finish_lt he hc
  have hl := hlower he
  rw [Nat.succ_mul] at hf
  omega

/-- One record is emitted per probe, independently of its kind and value. -/
def probeCount (probes : Call → ℕ) : List Call → ℕ
  | [] => 0
  | a :: xs => probes a + probeCount probes xs

theorem cost_eq_length_add_probes (probes : Call → ℕ) (xs : List Call) :
    cost probes xs = xs.length + probeCount probes xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [cost, ih, List.length_cons, probeCount]; omega

/-- The one initialization record and all probe records fit in the site's block. -/
theorem records_fit {probes : Call → ℕ} {H : ℕ} {xs : List Call}
    (hcost : cost probes xs < 2 * H) :
    1 + probeCount probes xs ≤ 4 * H := by
  rw [cost_eq_length_add_probes] at hcost
  omega

theorem Valid.block_bounds {probes : Call → ℕ} {H v start : ℕ} {blocks : List (List Call)}
    (hH : 0 < H) (hv : Valid probes H v start blocks)
    (hc : ∀ a ∈ blocks.flatten, 1 + probes a ≤ H) :
    ∀ xs ∈ blocks, cost probes xs < 2 * H ∧ 1 + probeCount probes xs ≤ 4 * H := by
  induction blocks generalizing v start with
  | nil => simp
  | cons xs blocks ih =>
    obtain ⟨hl, hb, _, ht⟩ := hv
    intro ys hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have h := site_cost_lt hH hl hb (fun a ha => hc a (by simp [ha]))
      exact ⟨h, records_fit h⟩
    · exact ih ht (fun a ha => hc a (by simp [ha])) ys hm

/-- With both of the paper's caps, the canonical site grouping satisfies the
local cost and record capacity bounds simultaneously. -/
theorem partition_block_bounds {probes : Call → ℕ} {S H : ℕ} {xs : List Call}
    (hH : 0 < H) (hcap : cost probes xs ≤ S * H) (hc : ∀ a ∈ xs, 1 + probes a ≤ H) :
    ∀ ys ∈ partition probes H 0 S 0 xs,
      cost probes ys < 2 * H ∧ 1 + probeCount probes ys ≤ 4 * H := by
  obtain ⟨hflat, hv⟩ := partition_spec (v := 0) (start := 0) (sites := S)
    (xs := xs) (fun _ => by simp) (by simpa using hcap)
  exact hv.block_bounds hH (by rw [hflat]; exact hc)

/-- If the final call consumes the entire cap, its start still belongs to
the last site. This applies equally to an accepting final call. -/
theorem last_site_at_cap {S H start probes : ℕ}
    (hcall : 1 + probes ≤ H) (hcap : start + (1 + probes) = (S + 1) * H) :
    start / H = S := by
  have hH : 0 < H := by omega
  have hl : S ≤ start / H := (Nat.le_div_iff_mul_le hH).mpr (by
    rw [Nat.succ_mul] at hcap
    omega)
  have hu : start / H < S + 1 := (Nat.div_lt_iff_lt_mul hH).mpr (by omega)
  omega

/-- At the last available unit, starting a call is possible exactly when
there are no subsequent probes in it. -/
theorem final_unit_iff {cap start probes : ℕ} (h : start + 1 = cap) :
    start + (1 + probes) ≤ cap ↔ probes = 0 := by omega

/-- A running continuation at the cap cannot start even a probe-free call. -/
theorem next_call_exceeds_cap (cap probes : ℕ) : cap < cap + (1 + probes) := by omega

end RAMBuckets

end VPVNP
end Computability
end OAI
