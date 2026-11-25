import OAI.Computability.BorderVNP.ShortenStaticRowCircuit
import OAI.Computability.BorderVNP.ShortenStaticRowHoles

/-! # Coupling the Boolean row serializer to the sewn network

The numeric source data need only specify old cables present in the
directory. Terminal addresses are used only for charged matched prefixes.
The padding address is the actual reserved site for this candidate slot.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows.Serializer

open Crossing SeedIntervals CombiningStep Packing.Names
open scoped Classical

/-- Read the source or destination public site number or the width of an actual network cable. -/
def fieldAt {D N : ℕ} {P : Type*} {bits : P → ℕ} (L : Network D P bits)
    (sites : L.Site ↪ Fin N) (z : L.Edge) : Column → ℕ
  | .src => (sites (L.src z)).val
  | .dst => (sites (L.dst z)).val
  | .width => L.width z

variable {D m nSites nEdges nSeeds : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
variable (oldSite : p.layout.Site ↪ Fin nSites) (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)
variable (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A)
variable (k : Fin 3) (r : Fin nEdges) (b : Band D) (flag : Flag → Bool) (v : Word → ℕ)

/-- Lookup data for one public candidate row, independent of the histogram branch. -/
structure Represents : Prop where
  /-- Occupancy of the old cable directory. -/
  occupied : flag .occupied = true ↔ r ∈ Set.range old
  /-- A cable is charged when its bin is present. -/
  charged : ∀ c, old c = r → flag .charged = (bin c).isSome
  /-- Orientation determines the terminal sign of each hook. -/
  orientation : ∀ c, old c = r → flag .positive = positive c
  /-- Public source site of the old cable. -/
  src : ∀ c, old c = r → v .oldSrc = (oldSite (p.layout.src c)).val
  /-- Public destination site of the old cable. -/
  dst : ∀ c, old c = r → v .oldDst = (oldSite (p.layout.dst c)).val
  /-- The span is the width of this band of the old cable. -/
  span : ∀ c, old c = r → v .span = (SeedIntervals.layout p.layout bin perm m).width (c,b)
  /-- The reserved padding-site address of this candidate. -/
  pad : v .pad = (siteRows e p oldSite seed (dummy (rowSlot (bandCandidate e nSeeds k r b)))).val
  /-- The two terminal addresses use the inverse direction permutation to recover the seed. -/
  terminal : ∀ c, old c = r → ∀ d, b = some (d,true) → ∀ a, bin c = some a → ∀ sign : Bool,
    v (if sign then .terminalPos else .terminalNeg) =
      (siteRows e p oldSite seed (.inr ⟨(perm d).symm a,.inr (.inl (d,sign))⟩)).val

/-- The numeric column at the candidate slot of the padded output on the given branch. -/
noncomputable abbrev paddedField (first : Fin D × Bool) (q : Counts e p bin perm) : Column → ℕ :=
  let L := (output e p bin perm positive first q).layout
  fieldAt (Packing.Names.layout L (outputRows e p bin perm positive first q old seed) dummy)
    (siteRows e p oldSite seed) (rowSlot (bandCandidate e nSeeds k r b))

variable {e p bin perm positive oldSite old seed dummy k r b flag v}

private theorem prefix_iff (b : Band D) : isPrefix b = true ↔ ∃ d, b = some (d,true) := by
  rcases b with _ | ⟨d,s⟩
  · simp [isPrefix]
  · cases s <;> simp [isPrefix]

/-- The Boolean enable bit detects membership in the range of the actual sewn output's names. -/
theorem Represents.enabled_iff
    (h : Represents e p bin perm positive oldSite old seed dummy k r b flag v) :
    enabled k (isPrefix b) flag = true ↔ bandCandidate e nSeeds k r b ∈ Set.range (edgeRows e p bin perm old seed) := by
  rw [bandCandidate_mem_iff]
  by_cases hr : r ∈ Set.range old
  · obtain ⟨c,rfl⟩ := hr
    have hch := h.charged c rfl
    have ho := h.occupied.mpr ⟨c,rfl⟩
    have hs : (c,b) ∈ (partition p.layout bin perm m).selected ↔ (bin c).isSome = true ∧ isPrefix b = true := by
      rw [selected_iff, prefix_iff]
    simp only [old.injective.eq_iff, exists_eq_left, hs, enabled, ho, Bool.true_and, hch]
    fin_cases k <;> cases (bin c).isSome <;> cases isPrefix b <;> decide
  · have hf : flag .occupied = false := by simpa only [Bool.not_eq_true] using h.occupied.not.mpr hr
    simp only [enabled,hf,Bool.false_and,Bool.false_eq_true,false_iff]
    exact fun ⟨c,hc,_⟩ => hr ⟨c,hc⟩

private theorem paddedField_occupied (first : Fin D × Bool) (q : Counts e p bin perm)
    (z : EdgeShape e p bin perm) (hz : edgeRows e p bin perm old seed z = bandCandidate e nSeeds k r b)
    (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A) (col : Column) :
    paddedField e p bin perm positive oldSite old seed dummy k r b first q col =
      fieldAt (output e p bin perm positive first q).layout (siteRows e p oldSite seed) z col := by
  let L := (output e p bin perm positive first q).layout
  let rows := outputRows e p bin perm positive first q old seed
  have hi : rowSlot (bandCandidate e nSeeds k r b) = slot L rows z := congrArg rowSlot hz.symm
  dsimp only [paddedField]
  rw [hi]
  cases col with
  | src => exact congrArg (fun v => (siteRows e p oldSite seed v).val) (src_slot L rows dummy z)
  | dst => exact congrArg (fun v => (siteRows e p oldSite seed v).val) (dst_slot L rows dummy z)
  | width => exact width_slot L rows dummy z

private theorem active_retained (h : Represents e p bin perm positive oldSite old seed dummy 2 r b flag v)
    (first : Fin D × Bool) (q : Counts e p bin perm) (c : p.layout.Edge) (hr : old c = r)
    (hn : (c,b) ∉ (partition p.layout bin perm m).selected) (col : Column) :
    activeWord 2 (flag .positive) v col = paddedField e p bin perm positive oldSite old seed dummy 2 r b first q col := by
  let z : {z : (SeedIntervals.layout p.layout bin perm m).Edge // z ∉ (partition p.layout bin perm m).selected} := ⟨(c,b),hn⟩
  have hz := retained_candidate e p bin perm old seed z
  rw [paddedField_occupied first q (.inr (.inl z)) (hz.trans (congrArg (fun j => bandCandidate e nSeeds 2 j b) hr))]
  cases col with
  | src => exact h.src c hr
  | dst => exact h.dst c hr
  | width => exact h.span c hr

private theorem active_hook (a : A) (d : Fin D) (c : {c : p.layout.Edge // bin c = some (perm d a)})
    (source : Bool) (hr : old c.val = r)
    (h : Represents e p bin perm positive oldSite old seed dummy (if source then 0 else 1) r (some (d,true)) flag v)
    (first : Fin D × Bool) (q : Counts e p bin perm) (col : Column) :
    activeWord (if source then 0 else 1) (flag .positive) v col =
      paddedField e p bin perm positive oldSite old seed dummy (if source then 0 else 1) r
        (some (d,true)) first q col := by
  let z := seedHook e p bin perm a d c source
  let t := partition p.layout bin perm m
  let u := t.includeEdge a (prefixEdge p.layout bin perm m a d c).val
  have hn : edgeRows e p bin perm old seed z =
      bandCandidate e nSeeds (if source then 0 else 1) r (some (d,true)) := by
    subst r
    cases source
    · exact (hook_candidate e p bin perm old seed u).2
    · exact (hook_candidate e p bin perm old seed u).1
  rw [paddedField_occupied first q z hn]
  obtain ⟨hs,hd,hw⟩ := hook_fields e p bin perm positive first q (fun a => (seed a).val) a d c source
  cases col with
  | width =>
    exact (h.span c.val hr).trans ((descriptor_width p.layout bin perm m (fun a => (seed a).val) c _).trans hw.symm)
  | src =>
    change _ = (siteRows e p oldSite seed ((output e p bin perm positive first q).layout.src z)).val
    rw [hs]
    cases source
    · exact h.dst c.val hr
    · exact h.src c.val hr
  | dst =>
    change _ = (siteRows e p oldSite seed ((output e p bin perm positive first q).layout.dst z)).val
    rw [hd]
    have hp := h.orientation c.val hr
    have hterm := h.terminal c.val hr d rfl (perm d a) c.property
    simp only [Equiv.symm_apply_apply] at hterm
    cases source <;> cases hc : positive c.val <;> rw [hc] at hp
    all_goals rw [hp]
    all_goals first | exact hterm true | exact hterm false

private theorem active_selected (source : Bool) (c : p.layout.Edge) (hr : old c = r)
    (hs : (c,b) ∈ (partition p.layout bin perm m).selected)
    (h : Represents e p bin perm positive oldSite old seed dummy (if source then 0 else 1) r b flag v)
    (first : Fin D × Bool) (q : Counts e p bin perm) (col : Column) :
    activeWord (if source then 0 else 1) (flag .positive) v col =
      paddedField e p bin perm positive oldSite old seed dummy (if source then 0 else 1) r b first q col := by
  obtain ⟨hch,d,rfl⟩ := (selected_iff p bin perm c b).mp hs
  cases ha : bin c with
  | none => simp [ha] at hch
  | some a =>
    let u : {u : p.layout.Edge // bin u = some (perm d ((perm d).symm a))} :=
      ⟨c, by simpa only [Equiv.apply_symm_apply] using ha⟩
    exact active_hook ((perm d).symm a) d u source hr h first q col

/-- The serializer reproduces the occupancy bit and all three numeric fields of every old-band
candidate on every histogram branch, including padding loops and zero-width selected hooks. -/
theorem Represents.correct (h : Represents e p bin perm positive oldSite old seed dummy k r b flag v)
    (first : Fin D × Bool) (q : Counts e p bin perm) :
    (enabled k (isPrefix b) flag = true ↔
      bandCandidate e nSeeds k r b ∈ Set.range (outputRows e p bin perm positive first q old seed)) ∧
    ∀ col, columnValue k (isPrefix b) flag v col =
      paddedField e p bin perm positive oldSite old seed dummy k r b first q col := by
  refine ⟨h.enabled_iff, fun col => ?_⟩
  by_cases active : enabled k (isPrefix b) flag = true
  · rw [columnValue,ite_eq_left active]
    obtain ⟨c,hr,hkind⟩ := (bandCandidate_mem_iff e p bin perm old seed k r b).mp (h.enabled_iff.mp active)
    fin_cases k
    · exact active_selected true c hr (hkind.mpr (by decide)) h first q col
    · exact active_selected false c hr (hkind.mpr (by decide)) h first q col
    · exact active_retained h first q c hr (fun hs => (by decide : ¬(2 : Fin 3).val < 2) (hkind.mp hs)) col
  · rw [columnValue,ite_eq_right active]
    have hn := (bandCandidate_mem_iff e p bin perm old seed k r b).not.mp (h.enabled_iff.not.mp active)
    obtain ⟨hs,hd,hw⟩ := bandCandidate_hole e p bin perm old seed positive first q dummy k r b hn
    cases col with
    | src => exact h.pad.trans (congrArg (fun v => (siteRows e p oldSite seed v).val) hs.symm)
    | dst => exact h.pad.trans (congrArg (fun v => (siteRows e p oldSite seed v).val) hd.symm)
    | width => exact hw.symm

end Shortening.StaticRows.Serializer

end BorderVNP
end Computability
end OAI
