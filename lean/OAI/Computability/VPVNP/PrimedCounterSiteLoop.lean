import OAI.Computability.VPVNP.PrimedCounterVisit
import Mathlib.Data.List.FinRange

/-!
# Accumulating all primed sites in one histogram

Every site gets its own empty mark array and its prescribed root frame. The
histogram passes from one site to the next. After the last site, comparing
the entire array against the nomination accepts precisely the binary tapes
whose joint production count equals the nominated histogram.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open ParseGrammar
open scoped Classical

variable {n m s w : ℕ} {Site : Type*}

/-- Ordered complete site parses, with only the histogram shared between them. -/
noncomputable def runSites (w : ℕ) (d : Fin n) (root : Fin s) (x : Site → Fin m → Bool)
    (bs : Site → List (List Bool)) :
    List Site → (Label n m (Fin s) →₀ ℕ) → Option (Label n m (Fin s) →₀ ℕ)
  | [], initial => some initial
  | v :: more, initial => do
    let st ← visits w (x v) ⟨[(d,root)], ∅, initial⟩ (bs v)
    runSites w d root x bs more st.counts

/-- Any site reached by a complete successful execution passes its own
mark and tree checks, even if the incoming histogram is nonzero. -/
theorem runSites_local (hn : n ≤ 2^w) (hm : m ≤ 2^w) (hs : s ≤ 2^w)
    (d : Fin n) (root : Fin s) (x : Site → Fin m → Bool) (bs : Site → List (List Bool))
    (rows : List Site) {initial final : Label n m (Fin s) →₀ ℕ}
    (he : runSites w d root x bs rows initial = some final) (v : Site) (hv : v ∈ rows) :
    ∃ ts, decodeVisits w (x v) [(d,root)] (bs v) = some ts ∧ (positions ts).Nodup := by
  induction rows generalizing initial with
  | nil => simp at hv
  | cons u more ih =>
    cases hrun : visits w (x u) ⟨[(d,root)], ∅, initial⟩ (bs u) with
    | none => simp [runSites, hrun] at he
    | some next =>
      rcases List.mem_cons.mp hv with rfl | ht
      · exact (visits_accepts (x v) d root initial (bs v) hn hm hs).1 (by rw [hrun]; rfl)
      · exact ih (by simpa [runSites, hrun] using he) ht

/-- Along arbitrary accepted branch tapes, the online shared histogram sums
the per-site increments in visit order. -/
theorem runSites_paths (hn : n ≤ 2^w) (hm : m ≤ 2^w) (hs : s ≤ 2^w)
    (d : Fin n) (root : Fin s) (x : Site → Fin m → Bool) (b : (v : Site) → SitePaths w (x v) d root)
    (rows : List Site) (initial : Label n m (Fin s) →₀ ℕ) :
    runSites w d root x (fun v => (b v).val) rows initial =
      some (initial + (rows.map (fun v => siteHistogram hm hs hn (x v) d root (b v))).sum) := by
  induction rows generalizing initial with
  | nil => simp [runSites]
  | cons v rows ih =>
    obtain ⟨marks, hrun⟩ := visits_counts (x v) d root initial (b v) hn hm hs
    simp [runSites, hrun, ih, add_assoc]

/-- At the final site every dense histogram component must agree with its
nomination. The linear comparison consumes no binary choice. -/
noncomputable def compareAll {T : ℕ} (values nominated : Fin T → ℕ) : Bool :=
  (List.finRange T).all (fun j => decide (values j = nominated j))

theorem compareAll_iff {T : ℕ} (values nominated : Fin T → ℕ) :
    compareAll values nominated = true ↔ values = nominated := by
  simp [compareAll, funext_iff]

/-- Each accepted site consumes exactly one word-choice list at each of
its `2*d+1` preorder visits. -/
theorem sitePaths_length (hn : n ≤ 2^w) (hm : m ≤ 2^w) (hs : s ≤ 2^w)
    (x : Fin m → Bool) (d : Fin n) (root : Fin s) (b : SitePaths w x d root) :
    b.val.length = 2*d.val + 1 := by
  obtain ⟨hd, hmark⟩ := chosenTokens_spec x d root b
  obtain ⟨hb, hsc⟩ := decodeVisits_sound hm hs hn _ _ _ _ hd
  have he := scan_root x d root (chosenTokens x d root b)
  cases hr : readTree x d.val (chosenTokens x d root b) with
  | none => simp [he, hr] at hsc
  | some v =>
    obtain ⟨p, tail⟩ := v
    obtain ⟨ha, ht⟩ := readTree_sound _ _ _ _ _ hr
    cases tail with
    | nil => simp [hb, ht]
    | cons t ts => simp [he, hr] at hsc

/-- Convert a path to its fixed-length array of per-node choice lists. -/
def siteArray (hn : n ≤ 2^w) (hm : m ≤ 2^w) (hs : s ≤ 2^w)
    (x : Fin m → Bool) (d : Fin n) (root : Fin s) (b : SitePaths w x d root) :
    Fin (2*d.val+1) → List Bool := fun i => b.val[i.val]'(by rw [sitePaths_length hn hm hs x d root b]; exact i.isLt)

theorem ofFn_siteArray (hn : n ≤ 2^w) (hm : m ≤ 2^w) (hs : s ≤ 2^w)
    (x : Fin m → Bool) (d : Fin n) (root : Fin s) (b : SitePaths w x d root) :
    List.ofFn (siteArray hn hm hs x d root b) = b.val := by
  apply List.ext_getElem (List.length_ofFn.trans (sitePaths_length hn hm hs x d root b).symm)
  intros
  simp only [List.getElem_ofFn, siteArray]

/-- The actual loop over the rows, restricted by the final full histogram
comparison, is parsimonious with the site path model. -/
noncomputable def siteLoopEquiv {S : ℕ} (hn : n ≤ 2^w) (hm : m ≤ 2^w) (hs : s ≤ 2^w)
    (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool) (μ : Label n m (Fin s) →₀ ℕ) :
    {raw : Fin S → Fin (2*d.val+1) → List Bool //
      runSites w d root x (fun v => List.ofFn (raw v)) (List.finRange S) 0 = some μ} ≃
    {b : (v : Fin S) → SitePaths w (x v) d root //
      ∑ v, siteHistogram hm hs hn (x v) d root (b v) = μ} where
  toFun raw := by
    let b (v : Fin S) : SitePaths w (x v) d root :=
      ⟨List.ofFn (raw.val v), runSites_local hn hm hs d root x _ _ raw.property v (by simp)⟩
    refine ⟨b, ?_⟩
    have he := (runSites_paths hn hm hs d root x b (List.finRange S) 0).symm.trans raw.property
    simpa [← List.ofFn_eq_map, List.sum_ofFn] using Option.some.inj he
  invFun b := by
    let raw (v : Fin S) := siteArray hn hm hs (x v) d root (b.val v)
    refine ⟨raw, ?_⟩
    simp only [raw, ofFn_siteArray]
    rw [runSites_paths hn hm hs d root x b.val, zero_add]
    simpa [← List.ofFn_eq_map, List.sum_ofFn] using congrArg some b.property
  left_inv raw := by apply Subtype.ext; funext i j; simp only [siteArray, List.getElem_ofFn]
  right_inv b := by
    apply Subtype.ext
    funext v
    apply Subtype.ext
    exact ofFn_siteArray hn hm hs (x v) d root (b.val v)

end PrimedCounter

end VPVNP
end Computability
end OAI
