import OAI.Computability.VPVNP.PairTraversalLevelDirectories

/-!
# Directory witnesses from native placement scans

The physical owner computation may implement the selected placement by a
different function on unused word values. On all live identifiers the two
ordered scans agree, giving the exact input directory to the row worker.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open BurstRAM CompressorRecords LocalHistory NetworkKernel Compression
open scoped Fin.CommRing

variable {w : ℕ} {A : Type*} [CommRing A] {N : Network} (t : Term A N)

private theorem siteWord_entry {I : Type} (o : Order I) (x : Word w) (h : x.val < o.length) :
    siteWord w o (o.entries ⟨x.val, h⟩) = x := by
  apply Fin.ext
  simp [siteWord]

open Classical in
/-- A native scan of a word-level placement that agrees on every actual site
gives exactly the directory of the mathematical term. -/
def Directory.ofPhysical (old : Order N.Site) (next : Order t.output.Site) (pub : Fin 6 → Word w)
    (raw : Memory w) (limit : ℕ) (h₀ : (pub 0).val = old.length) (h₁ : (pub 2).val = next.length)
    (regions : RowRegions pub) (bounds : (pub 5).val + (pub 2).val * (pub 4).val ≤ limit)
    (p : Word w → Word w) (hp : RepresentsPlacement old next t.place p)
    (hs : PreimagesAt pub p raw old.length)
    (capacity : ∀ v, Fintype.card (t.Preimage v) ≤ (pub 4).val) :
    Directory t old next raw limit := by
  let actual : Word w → Word w := encodedPlacement old.entries.symm next.entries.symm t.place
  have ho : old.length ≤ 2 ^ w := h₀ ▸ (pub 0).isLt.le
  have hn : next.length ≤ 2 ^ w := h₁ ▸ (pub 2).isLt.le
  have ha := encodedPlacement_represents old next t.place (w := w) ho hn
  have fiberRow (v : Word w) (hv : v < pub 2) (q : Word w → Word w)
      (hq : RepresentsPlacement old next t.place q) :
      let y := next.entries ⟨v.val, (show v.val < (pub 2).val from hv).trans_eq h₁⟩
      preimagePrefix q v old.length =
        orderedIds w old (fun u => y = t.place u) (old.restrict _) := by
    let y := next.entries ⟨v.val, (show v.val < (pub 2).val from hv).trans_eq h₁⟩
    have h := preimagePrefix_eq_orderedIds old next t.place q hq ho hn y
    rwa [siteWord_entry next v _] at h
  refine ⟨pub, h₀, h₁, regions, bounds, ⟨fun i hi => ?_, fun v hv => ?_⟩, fun v hv => ?_⟩
  · let u := old.entries ⟨i.val, (show i.val < (pub 0).val from hi).trans_eq h₀⟩
    have eq := (hp u).trans (ha u).symm
    rw [siteWord_entry old i _] at eq
    exact (hs.owners i hi).trans eq
  · rw [fiberRow v hv actual ha, ← fiberRow v hv p hp]
    exact hs.rows v hv
  · let y := next.entries ⟨v.val, (show v.val < (pub 2).val from hv).trans_eq h₁⟩
    rw [fiberRow v hv actual ha, orderedIds, List.length_ofFn]
    have card := Fintype.card_congr (old.restrict (fun u => y = t.place u)).entries
    rw [Fintype.card_fin] at card
    exact card.trans_le (capacity y)

open private placementLayer from OAI.Computability.VPVNP.PairTraversalStageSize

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → A)
variable (hf : B.IsSolution f) {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n)
variable (X : State (S.degreeExponent 0) n) (z : (B.execute f hf T hT X).Choices)

open Classical in
/-- The selected record limit bounds each actual placement fiber, including
fibers of size zero. It therefore supplies the raw scanner's capacity. -/
theorem selected_fiber_capacity (v : SelectedLevel B f hf) (hv : v ∈ executeLevels B f hf T hT X z)
    (y : (v.pass.step.term v.term).output.Site) :
    Fintype.card ((v.pass.step.term v.term).Preimage y) ≤ B.recordLimit := by
  classical
  let t := v.pass.step.term v.term
  let old := siteOrder v.input
  let next : Order t.output.Site := (v.pass.output_eq v.term).symm ▸ siteOrder (v.pass.next v.term)
  have hm : levelLayer B f hf v ∈ selectedLayers B f hf T hT X z := by
    rw [selectedLayers_eq_levels]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem hv)
  have h := selected_capacity B f hf T hT X z _ hm (next.entries.symm y)
  simp only [levelLayer, placementLayer, List.length_ofFn] at h
  change (old.restrict (fun u => next.entries (next.entries.symm y) = t.place u)).length ≤ _ at h
  rw [Equiv.apply_symm_apply] at h
  have card := Fintype.card_congr (old.restrict (fun u => y = t.place u)).entries
  rw [Fintype.card_fin] at card
  exact card.symm.trans_le h

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
