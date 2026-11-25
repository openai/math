import Mathlib.Data.Finset.Card

namespace OAI
/-! # The first pass of the concentrator

Each active left slot tries its candidate right slots in order. The algorithm
returns the matching, the skipped left slots and the remaining free right slots.
The skipped slots have no edge to a remaining free slot.
-/

namespace ThreeFlat.Concentrator.Greedy

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

structure Result (L R : Type*) where
  matched : List (L × R)
  missed : Finset L
  free : Finset R

def firstFree (candidates : List R) (free : Finset R) : Option R :=
  candidates.find? fun r => decide (r ∈ free)

/-- Only the flags at the listed candidates can affect a local choice. -/
theorem firstFree_congr (candidates : List R) {F F' : Finset R}
    (flags : ∀ r ∈ candidates, r ∈ F ↔ r ∈ F') : firstFree candidates F = firstFree candidates F' := by
  induction candidates with
  | nil => rfl
  | cons r rs ih =>
    have hr := flags r (by simp)
    have htail := ih (fun q hq => flags q (List.mem_cons_of_mem _ hq))
    by_cases hc : r ∈ F
    · simp [firstFree, hc, hr.mp hc]
    · simpa [firstFree, hc, mt hr.mpr hc] using htail

def run (N : L → List R) : List L → Finset R → Result L R
  | [], F => ⟨[], ∅, F⟩
  | x :: xs, F =>
    match firstFree (N x) F with
    | none =>
      let out := run N xs F
      {out with missed := insert x out.missed}
    | some r =>
      let out := run N xs (F.erase r)
      {out with matched := (x,r) :: out.matched}

/-- A certificate prescribes a choice at each active slot. Verification tests
the flags at its candidates and reserves the reported slot for that step. -/
def Valid (N : L → List R) (report : L → Option R) : List L → Finset R → Prop
  | [], _ => True
  | x :: xs, F => report x = firstFree (N x) F ∧
      Valid N report xs (match report x with | none => F | some r => F.erase r)

def reportedFree (N : L → List R) (report : L → Option R) (prior : List L) (F : Finset R) :
    Finset R :=
  F.filter fun r => prior.all fun q => decide (r ∈ N q → report q ≠ some r)

omit [DecidableEq L] in
private theorem reportedFree_cons (N : L → List R) (f : L → Option R) (prior : List L)
    (F : Finset R) (x : L) (valid : f x = firstFree (N x) F) :
    reportedFree N f (x :: prior) F =
      reportedFree N f prior (match f x with | none => F | some r => F.erase r) := by
  ext a
  cases hx : f x with
  | none => simp [reportedFree, hx]
  | some r =>
    have hn : r ∈ N x := List.mem_of_find?_eq_some (valid.symm.trans hx)
    by_cases eq : a = r
    · subst a
      simp [reportedFree, hx, hn]
    · simp [reportedFree, hx, eq, Ne.symm eq]

/-- Local verification only needs to inspect the earlier contenders for each
candidate. An earlier slot with that candidate marks it taken exactly when
it reports a match to that slot. -/
def LocalValid (N : L → List R) (f : L → Option R) (xs : List L) (F : Finset R) : Prop :=
  ∀ (prior : List L) (x : L) (later : List L), xs = prior ++ x :: later →
    f x = firstFree (N x) (reportedFree N f prior F)

omit [DecidableEq L] in
theorem localValid_iff_valid (N : L → List R) (f : L → Option R) (xs : List L) (F : Finset R) :
    LocalValid N f xs F ↔ Valid N f xs F := by
  induction xs generalizing F with
  | nil => simp [LocalValid, Valid]
  | cons x xs ih =>
    constructor
    · intro loc
      have hx : f x = firstFree (N x) F := by
        simpa [reportedFree] using loc [] x xs rfl
      refine ⟨hx, (ih _).mp ?_⟩
      intro p q s hs
      have hq := loc (x :: p) q s (by simp [hs])
      rwa [reportedFree_cons N f p F x hx] at hq
    · intro ok p q s h
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simpa [reportedFree] using ok.1
      | cons y p =>
        simp only [List.cons_append, List.cons.injEq] at h
        rcases h with ⟨rfl, hs⟩
        rw [reportedFree_cons N f p F x ok.1]
        exact (ih _).mpr ok.2 p q s hs

omit [DecidableEq L] in
theorem valid_unique {N : L → List R} {f g : L → Option R} {xs : List L} {F : Finset R}
    (hf : Valid N f xs F) (hg : Valid N g xs F) : ∀ x ∈ xs, f x = g x := by
  induction xs generalizing F with
  | nil => simp
  | cons x xs ih =>
    have h : f x = g x := hf.1.trans hg.1.symm
    have ht := hf.2
    rw [h] at ht
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h
    · exact ih ht hg.2 q hq

omit [DecidableEq L] in
theorem valid_congr {N : L → List R} {f g : L → Option R} {xs : List L} {F : Finset R}
    (hf : Valid N f xs F) (eq : ∀ x ∈ xs, f x = g x) : Valid N g xs F := by
  induction xs generalizing F with
  | nil => trivial
  | cons x xs ih =>
    have h := eq x (by simp)
    refine ⟨h.symm.trans hf.1, ?_⟩
    rw [← h]
    exact ih hf.2 (fun q hq => eq q (List.mem_cons_of_mem _ hq))

/-- Every legal (duplicate-free) processing order has a valid local report. -/
theorem exists_valid (N : L → List R) (xs : List L) (F : Finset R) (hd : xs.Nodup) :
    ∃ f : L → Option R, Valid N f xs F := by
  induction xs generalizing F with
  | nil => exact ⟨fun _ => none, trivial⟩
  | cons x xs ih =>
    have hd' := List.nodup_cons.mp hd
    let c := firstFree (N x) F
    obtain ⟨f, hf⟩ := ih (match c with | none => F | some r => F.erase r) hd'.2
    let g := fun q => if q = x then c else f q
    have hx : g x = c := by simp [g]
    refine ⟨g, hx, ?_⟩
    rw [hx]
    exact valid_congr hf fun q hq => by
      have hn : q ≠ x := fun h => hd'.1 (h ▸ hq)
      simp [g, hn]

/-- Inactive slots report no match, so padding is uniquely determined as well. -/
def PaddedLocalValid (N : L → List R) (report : L → Option R) (xs : List L) (F : Finset R) : Prop :=
  LocalValid N report xs F ∧ ∀ x ∉ xs, report x = none

theorem existsUnique_paddedLocalValid (N : L → List R) (xs : List L) (F : Finset R)
    (hd : xs.Nodup) : ∃! f, PaddedLocalValid N f xs F := by
  obtain ⟨f, hf⟩ := exists_valid N xs F hd
  let g := fun x => if x ∈ xs then f x else none
  have ok : Valid N g xs F := valid_congr hf (fun x hx => by simp [g, hx])
  refine ⟨g, ⟨(localValid_iff_valid ..).mpr ok, fun x hx => by simp [g, hx]⟩, ?_⟩
  intro g' h
  funext x
  by_cases hx : x ∈ xs
  · exact valid_unique ((localValid_iff_valid ..).mp h.1) ok x hx
  · simp [g, hx, h.2 x hx]

/-- A valid report determines exactly which pairs the algorithm matched and which
left slots it handed to the reserve. -/
theorem valid_iff_result {N : L → List R} {xs : List L} {F : Finset R}
    {f : L → Option R} (ok : Valid N f xs F) (q : L) :
    (∀ a : R, (q,a) ∈ (run N xs F).matched ↔ q ∈ xs ∧ f q = some a) ∧
      (q ∈ (run N xs F).missed ↔ q ∈ xs ∧ f q = none) := by
  induction xs generalizing F with
  | nil => simp [run]
  | cons x xs ih =>
    cases h : firstFree (N x) F with
    | none =>
      have hx := ok.1.trans h
      have ht := ok.2
      rw [hx] at ht
      have spec := ih ht
      by_cases eq : q = x
      · subst q
        simp [run, h, hx, spec.1, spec.2]
      · simp [run, h, eq, spec.1, spec.2]
    | some r =>
      have hx := ok.1.trans h
      have ht := ok.2
      rw [hx] at ht
      have spec := ih ht
      by_cases eq : q = x
      · subst q
        simp [run, h, hx, spec.1, spec.2, eq_comm]
      · simp [run, h, eq, spec.1, spec.2]

structure Invariants (N : L → List R) (xs : List L) (F : Finset R) (out : Result L R) : Prop where
  free_subset : out.free ⊆ F
  enough_free : F.card ≤ out.free.card + xs.length
  missed_subset : ∀ x ∈ out.missed, x ∈ xs
  no_edge : ∀ x ∈ out.missed, ∀ r ∈ out.free, r ∉ N x
  used_free : ∀ e ∈ out.matched, e.2 ∈ F
  used_neighbor : ∀ e ∈ out.matched, e.2 ∈ N e.1
  distinct_rights : (out.matched.map Prod.snd).Nodup

theorem run_invariants (N : L → List R) (xs : List L) (F : Finset R) :
    Invariants N xs F (run N xs F) := by
  induction xs generalizing F with
  | nil => simp [run]; constructor <;> simp
  | cons x xs ih =>
    cases h : firstFree (N x) F with
    | none =>
      have spec := ih F
      have noFree : ∀ r ∈ N x, r ∉ F := by simpa [firstFree] using h
      simp only [run, h]
      refine ⟨spec.free_subset, ?_, ?_, ?_, spec.used_free, spec.used_neighbor, spec.distinct_rights⟩
      · have room := spec.enough_free
        simp only [List.length_cons]
        omega
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (spec.missed_subset _ hq)
      · intro q hq r hr
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact fun hn => noFree _ hn (spec.free_subset hr)
        · exact spec.no_edge _ hq r hr
    | some r =>
      have spec := ih (F.erase r)
      have hr : r ∈ F := by simpa [firstFree] using List.find?_some h
      have hn : r ∈ N x := List.mem_of_find?_eq_some h
      simp only [run, h]
      refine ⟨spec.free_subset.trans (Finset.erase_subset _ _), ?_, ?_, spec.no_edge, ?_, ?_, ?_⟩
      · have count := Finset.card_erase_add_one hr
        have room := spec.enough_free
        simp only [List.length_cons]
        omega
      · exact fun q hq => List.mem_cons_of_mem _ (spec.missed_subset q hq)
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hr
        · exact (Finset.erase_subset _ _) (spec.used_free _ he)
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hn
        · exact spec.used_neighbor _ he
      · simpa only [List.map_cons, List.nodup_cons] using
          (show r ∉ (run N xs (F.erase r)).matched.map Prod.snd ∧
              ((run N xs (F.erase r)).matched.map Prod.snd).Nodup from
            ⟨by
              intro hmem
              obtain ⟨e, he, eq⟩ := List.mem_map.mp hmem
              exact (Finset.mem_erase.mp (spec.used_free _ he)).1 eq,
             spec.distinct_rights⟩)

/-- With enough right slots left free, mixing rules out a large unassigned set. -/
theorem missed_card_lt_of_mixing (N : L → List R) (xs : List L) (F : Finset R)
    (threshold : ℕ) (slack : xs.length + threshold ≤ F.card)
    (mix : ∀ (A : Finset L) (B : Finset R),
      (∀ x ∈ A, x ∈ xs) → B ⊆ F → threshold ≤ A.card → threshold ≤ B.card →
      ∃ x ∈ A, ∃ r ∈ B, r ∈ N x) :
    (run N xs F).missed.card < threshold := by
  have spec := run_invariants N xs F
  have room := spec.enough_free
  by_contra! hlarge
  obtain ⟨x, hx, r, hr, hxr⟩ := mix _ _ spec.missed_subset spec.free_subset hlarge (by omega)
  exact spec.no_edge _ hx _ hr hxr

end ThreeFlat.Concentrator.Greedy

end OAI
