import OAI.Computability.VPVNP.PairTraversalNativeRows
import OAI.Computability.VPVNP.PairTraversalLayerExecution

/-!
# Translating the complete preimage directory of a selected term

Every old position occurs in one placement fiber. After the placement scan
has collected those fibers in old-site order, the descriptor builder reads
and translates each identifier once and publishes one header per new site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open NetworkKernel LocalHistory BurstRAM CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ} {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N : Network} {t : Term A N}

private theorem valid_owner {n : ℕ} {pub : Fin 6 → Word w}
    (h : (pub 2).val = n) (i : Fin n) : (i.val : Word w) < pub 2 := by
  change i.val % (2 ^ w) < (pub 2).val
  have hi : i.val < (pub 2).val := h ▸ i.isLt
  rw [Nat.mod_eq_of_lt (hi.trans (pub 2).isLt)]
  exact hi

open Classical in
/-- All source rows expected by the native layer builder occur in the completed
placement directory. The order of each row is the selected local reader's order. -/
theorem raw_rows_of_preimages (old : Order N.Site) (next : Order t.output.Site)
    (r : TermParsers κ t) (physical : Word w → Word w)
    (realizes : RepresentsPlacement old next t.place physical)
    (hchildren : ∀ v, r.order.children v = old.restrict (fun u => v = t.place u))
    (pub : Fin 6 → Word w) (mem : Memory w)
    (oldCount : (pub 0).val = old.length) (newCount : (pub 2).val = next.length)
    (collected : PreimagesAt pub physical mem old.length) :
    ∀ i : Fin next.length, rowRepresents mem (countAt pub (i.val : Word w))
      (rowAt pub (i.val : Word w))
      (((stepLayer old next r).ids i).map (fun j : ℕ => (j : Word w))) := by
  intro i
  have ho : old.length ≤ 2 ^ w := oldCount ▸ (pub 0).isLt.le
  have hn : next.length ≤ 2 ^ w := newCount ▸ (pub 2).isLt.le
  have eqn := preimagePrefix_eq_orderedIds old next t.place physical realizes ho hn (next.entries i)
  rw [← hchildren] at eqn
  simp only [siteWord, Equiv.symm_apply_apply, Fin.ofNat_eq_cast] at eqn
  have row := collected.rows (i.val : Word w) (valid_owner newCount i)
  rw [eqn] at row
  convert row using 1
  simp only [stepLayer, List.map_ofFn, orderedIds]
  congr 1

open private countAt_val rowAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan

/-- The whole source row, including any unused slots, is below the next layer's base.
The corresponding count is strictly below that base even if the row capacity is zero. -/
theorem preimage_input_before {pub : Fin 6 → Word w} {base : ℕ} (regions : RowRegions pub)
    (inputEnd : (pub 5).val + (pub 2).val * (pub 4).val ≤ base) {v : Word w}
    (hv : v < pub 2) : (countAt pub v).val < base ∧ (rowAt pub v).val + (pub 4).val ≤ base := by
  rw [countAt_val regions hv, rowAt_val regions hv]
  have before := regions.countsBeforeRows
  have room := Nat.mul_le_mul_right (pub 4).val (show v.val + 1 ≤ (pub 2).val from hv)
  rw [Nat.succ_mul] at room
  change v.val < (pub 2).val at hv
  omega

/-- The placement fibers partition the old positions. -/
theorem stepLayer_sum_ids_length (old : Order N.Site)
    (next : Order t.output.Site) (r : TermParsers κ t) :
    ∑ i : Fin next.length, ((stepLayer old next r).ids i).length = old.length := by
  classical
  simp only [stepLayer, List.length_ofFn]
  calc
    _ = ∑ v : t.output.Site, Fintype.card (t.Preimage v) :=
      Fintype.sum_equiv next.entries _ _ (fun i => by
        simpa only [Fintype.card_fin] using
          Fintype.card_congr (r.order.children (next.entries i)).entries)
    _ = Fintype.card N.Site := by
      rw [← Fintype.card_sigma]
      apply Fintype.card_congr
      exact
        { toFun := fun p => p.2.val
          invFun := fun u => ⟨t.place u, ⟨u, rfl⟩⟩
          left_inv := fun ⟨v, ⟨u, h⟩⟩ => by cases h; rfl
          right_inv := fun _ => rfl }
    _ = old.length := by simpa only [Fintype.card_fin] using Fintype.card_congr old.entries.symm

open Classical in
/-- Build one selected term's descriptor layer from its completed preimage pass.
Every old site costs one read and one write, and every new site costs three
header probes. The capacity bounds apply separately to the source directory
and to the reserved destination rows. -/
theorem native_step_layer (old : Order N.Site) (next : Order t.output.Site)
    (r : TermParsers κ t) (physical : Word w → Word w)
    (realizes : RepresentsPlacement old next t.place physical)
    (hchildren : ∀ v, r.order.children v = old.restrict (fun u => v = t.place u))
    (pub : Fin 6 → Word w) (mem : Memory w)
    (oldCount : (pub 0).val = old.length) (newCount : (pub 2).val = next.length)
    (collected : PreimagesAt pub physical mem old.length)
    (state : Word w) (priv : Word w → Word w) (cap previous base : ℕ) (regions : RowRegions pub)
    (inputEnd : (pub 5).val + (pub 2).val * (pub 4).val ≤ base)
    (capacity : ∀ i, ((stepLayer old next r).ids i).length ≤ min (pub 4).val cap)
    (fit : endPos cap base (stepLayer old next r) < 2 ^ w) :
    let L := stepLayer old next r
    let counts := fun i : Fin next.length => countAt pub (i.val : Word w)
    let starts := fun i : Fin next.length => rowAt pub (i.val : Word w)
    ∃ es, LayerPasses L cap previous base state priv counts starts (List.finRange next.length)
        mem es ∧ after mem es = writeLayer cap previous base L mem ∧
      countProbes es = 2 * old.length + 3 * next.length := by
  let L := stepLayer old next r
  have before (i : Fin next.length) :=
    preimage_input_before regions inputEnd (valid_owner newCount i)
  obtain ⟨es, run, image, probes⟩ :=
    native_layer L cap previous base state priv _ _ mem
      (raw_rows_of_preimages old next r physical realizes hchildren pub mem oldCount newCount
        collected)
      (fun i => (before i).1)
      (fun i => (Nat.add_le_add_left ((le_min_iff.mp (capacity i)).1) _).trans (before i).2)
      (fun i => (le_min_iff.mp (capacity i)).2) fit
  refine ⟨es, run, image, ?_⟩
  have total : ∑ i : Fin L.count, (L.ids i).length = old.length :=
    stepLayer_sum_ids_length old next r
  rw [probes, total]
  rfl

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
