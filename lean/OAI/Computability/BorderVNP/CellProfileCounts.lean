import OAI.Computability.BorderVNP.CellPrefixCount

/-!
# Prefix flags certify a histogram and the ranks on every routed cable

For each selector term the auxiliary rectangle records its count before each copy.
The final row certifies the advertised histogram, and the row at the source copy
gives its index on the compact cable. The selector and all lane bits stay fixed
when these auxiliary flags are guessed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Profile

open Prefix

/-- Private Boolean flags indexed by term, prefix length and candidate occurrence count. -/
abbrev Flags := ℕ → ℕ → ℕ → Bool

/-- Size of the allocated flag block. -/
def auxSize (copies terms : ℕ) := terms * ((copies+1)*(copies+1))

/-- Row-major origin for one term's private prefix table. -/
def termBase (base copies term : ℕ) := base + term * ((copies+1)*(copies+1))

/-- The labelled bit table viewed inside the physical value stack. -/
def bankFlags (bank : ℕ → Bool) (base copies : ℕ) : Flags := fun t i k =>
  bank (address (termBase base copies t) copies i k)

/-- Match sequence for a single label in the fixed selector word. -/
def selects (bank : ℕ → Bool) (s : Port) (w t i : ℕ) := decide (label bank s w i = t)

/-- Prefix flags count exactly the strict predecessors used in the manuscript's route. -/
theorem count_matches (bank : ℕ → Bool) (s : Port) (w t i : ℕ) :
    count (selects bank s w t) i = earlier bank s w t i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [count, ih]
    by_cases h : t = label bank s w i <;> simp [earlier, List.range_succ, selects, h, eq_comm]

/-- Initialization, transitions and final value for an advertised term count. -/
def CountCheck (bank : ℕ → Bool) (copies : ℕ) (s : Port) (w t advertised : ℕ)
    (flags : Flags) : Prop :=
  Valid copies copies (selects bank s w t) (flags t) ∧
    advertised ≤ copies ∧ flags t copies advertised = true

/-- A selected copy uses the unique active prefix-count flag to compare its
original and compact cable lanes. -/
def RouteCheck (bank : ℕ → Bool) (copies : ℕ) (s : Port) (w terms : ℕ) (flags : Flags) (r : Route) : Prop :=
  r.term < terms ∧ ∀ i < copies, ∀ k ≤ copies, ∀ lane < r.lanes,
    label bank s w i = r.term → flags r.term i k = true →
      bank (r.original.atBit i lane) = bank (r.compact.atBit k lane)

/-- Denotation of the compiled checker, including its auxiliary flags. -/
def Accept (bank : ℕ → Bool) (copies : ℕ) (s : Port) (w : ℕ)
    (hist : List ℕ) (routes : List Route) (flags : Flags) : Prop :=
  (∀ i < copies, label bank s w i < hist.length) ∧
  (∀ t : Fin hist.length, CountCheck bank copies s w t.val hist[t] flags) ∧
  ∀ r ∈ routes, RouteCheck bank copies s w hist.length flags r

/-- Every flag of a passing checker is the Boolean equality to the exact occurrence
rank. The remaining constraints are precisely the original sparse profile semantics. -/
theorem accept_iff (bank : ℕ → Bool) (copies : ℕ) (s : Port) (w : ℕ)
    (hist : List ℕ) (routes : List Route) (flags : Flags) :
    Accept bank copies s w hist routes flags ↔
      profileValid bank copies s w hist routes ∧
      ∀ t < hist.length, ∀ i ≤ copies, ∀ k ≤ copies,
        flags t i k = decide (earlier bank s w t i = k) := by
  constructor
  · rintro ⟨hr,hc,hl⟩
    have correct (t : ℕ) (ht : t < hist.length) (i : ℕ) (hi : i ≤ copies) (k : ℕ) (hk : k ≤ copies) :
        flags t i k = decide (earlier bank s w t i = k) := by
      simpa only [count_matches] using (valid_iff copies copies _ _).mp (hc ⟨t,ht⟩).1 i hi k hk
    refine ⟨⟨hr,?_,?_⟩,correct⟩
    · intro t
      have hh := (hc t).2.2
      rw [correct _ t.isLt _ le_rfl _ (hc t).2.1, decide_eq_true_eq] at hh
      exact hh
    · intro r hm
      have h := hl r hm
      refine ⟨h.1,?_⟩
      intro i hi hm lane hl
      have hk : earlier bank s w r.term i ≤ copies :=
        (count_matches bank s w r.term i) ▸ (count_le _ i).trans hi.le
      exact h.2 i hi _ hk lane hl hm (by rw [correct _ h.1 _ hi.le _ hk]; simp)
  · rintro ⟨⟨hr,hc,hl⟩,correct⟩
    refine ⟨hr,?_,?_⟩
    · intro t
      have hk : hist[t] ≤ copies := by
        rw [← hc t, ← count_matches]; exact count_le _ _
      refine ⟨(valid_iff ..).mpr ?_, hk, ?_⟩
      · intro i hi k hk
        rw [count_matches]; exact correct _ t.isLt _ hi _ hk
      · rw [correct _ t.isLt _ le_rfl _ hk, hc t]; simp
    · intro r hm
      have h := hl r hm
      refine ⟨h.1, ?_⟩
      intro i hi k hk lane hLane hs hflag
      rw [correct _ h.1 _ hi.le _ hk,decide_eq_true_eq] at hflag
      rw [← hflag]
      exact h.2 _ hi hs _ hLane

/-- Zero-extended lookup of the finite private flag cube. -/
def get {terms copies : ℕ} (f : Fin terms → Fin (copies+1) → Fin (copies+1) → Bool) : Flags :=
  fun t i k => if ht : t < terms then getFlags (f ⟨t,ht⟩) i k else false

/-- A fixed data bank has exactly one satisfying choice of the private flags precisely
when the original profile is valid. Every finite flag position is forced. -/
theorem existsUnique_accept_iff (bank : ℕ → Bool) (copies : ℕ) (s : Port) (w : ℕ)
    (hist : List ℕ) (routes : List Route) :
    (∃! f : Fin hist.length → Fin (copies+1) → Fin (copies+1) → Bool,
      Accept bank copies s w hist routes (get f)) ↔ profileValid bank copies s w hist routes := by
  constructor
  · rintro ⟨f,h,_⟩
    exact ((accept_iff ..).mp h).1
  · intro h
    refine ⟨fun t i k => decide (earlier bank s w t i = k), (accept_iff ..).mpr ⟨h,?_⟩, ?_⟩
    · intro t ht i hi k hk; simp [get,getFlags,ht,hi,hk]
    · intro f hf; funext t i k
      have hi : i.val ≤ copies := by omega
      have hk : k.val ≤ copies := by omega
      simpa [get,getFlags,t.isLt,hi,hk] using ((accept_iff ..).mp hf).2 t t.isLt i hi k hk

end CellSparse.Profile

end BorderVNP
end Computability
end OAI
