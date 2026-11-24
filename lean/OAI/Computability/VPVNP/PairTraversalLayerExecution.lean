import OAI.Computability.VPVNP.PairTraversalRows
import OAI.Computability.VPVNP.PairTraversalRowExecution

/-!
# Native identifier translation over a complete descriptor layer

Scan and header routines are run once per site. All counts and source lists are
below the destination layer. Each call writes just its two header words and its
live children, so source records survive every visit and row padding retains
its initial contents.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open BurstRAM CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

/-- The two native routines for every site in the supplied order, passing the
actual external memory and concatenating their emitted events. -/
inductive LayerPasses (L : Layer) (cap previous base : ℕ) (state : Word w)
    (priv : Word w → Word w) (counts starts : Fin L.count → Word w) :
    List (Fin L.count) → Memory w → List (Event w) → Prop
  | nil (m : Memory w) : LayerPasses L cap previous base state priv counts starts [] m []
  | cons {i is m ss es}
      (site : DescriptorRows.NativePass Fin.elim0 state priv m
        (address cap base i.val) (starts i).val (address cap base i.val + 2)
        (counts i) (previous : Word w) ((cap + 2 : ℕ) : Word w)
        ((L.ids i).map (fun j : ℕ => (j : Word w))) ss)
      (tail : LayerPasses L cap previous base state priv counts starts is (after m ss) es) :
      LayerPasses L cap previous base state priv counts starts (i :: is) m (ss ++ es)

private def live (L : Layer) (cap base : ℕ) (i : Fin L.count) (x : ℕ) : Prop :=
  address cap base i.val ≤ x ∧ x < address cap base i.val + 2 + (L.ids i).length

private theorem agree_row {m m' : Memory w} {n : ℕ} {kids : List (Word w)}
    (h : DFS.Row m n (n + 2) kids) (h' : DFS.Row m' n (n + 2) kids)
    (x : ℕ) (lo : n ≤ x) (hi : x < n + 2 + kids.length) : m x = m' x := by
  rcases Nat.eq_or_lt_of_le lo with rfl | hx
  · exact h.2.2.1.trans h'.2.2.1.symm
  rcases Nat.eq_or_lt_of_le hx with rfl | hx
  · exact h.2.2.2.1.trans h'.2.2.2.1.symm
  let j : Fin kids.length := ⟨x - (n + 2), by omega⟩
  have eqn : n + 2 + j.val = x := by dsimp [j]; omega
  exact eqn ▸ (h.2.2.2.2 j).trans (h'.2.2.2.2 j).symm

private theorem pass_outside {L : Layer} {cap previous base : ℕ} {state : Word w}
    {priv : Word w → Word w} {m : Memory w} {i : Fin L.count} {start : ℕ} {count : Word w}
    {ss : List (Event w)}
    (h : DescriptorRows.NativePass Fin.elim0 state priv m
      (address cap base i.val) start (address cap base i.val + 2) count
      (previous : Word w) ((cap + 2 : ℕ) : Word w) ((L.ids i).map (fun j : ℕ => (j : Word w))) ss)
    (x : ℕ) (hx : ¬ live L cap base i x) : after m ss x = m x := by
  let n := address cap base i.val
  have hn : n + 1 < 2 ^ w := h.row.1
  change ¬ (n ≤ x ∧ x < n + 2 + (L.ids i).length) at hx
  rw [h.memory]
  change DescriptorRows.passMemory m n start (n + 2) count _ _ _ x = m x
  simp only [DescriptorRows.passMemory, DescriptorRows.rowMemory, writeMemory, Fin.val_natCast,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : n < 2 ^ w), List.length_map,
    ite_eq_right (by omega : x ≠ n), ite_eq_right (by omega : x ≠ n + 1),
    ite_eq_right (by omega : ¬ (n + 2 ≤ x ∧ x < n + 2 + (L.ids i).length))]

private theorem scanned_addresses (L : Layer) (i : Fin L.count) (cap previous : ℕ) :
    ((L.ids i).map (fun j : ℕ => (j : Word w))).map
      (DescriptorRows.address (previous : Word w) ((cap + 2 : ℕ) : Word w)) =
      childWords w cap previous L i := by
  unfold childWords
  rw [List.map_map]
  congr 1
  funext j
  simp only [DescriptorRows.address, Function.comp_apply, address, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

private theorem append_probes (ss es : List (Event w)) :
    countProbes (ss ++ es) = countProbes ss + countProbes es := by
  induction ss with
  | nil => simp [countProbes]
  | cons e ss ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

open private row_end_le from OAI.Computability.VPVNP.PairTraversalRows

/-- Running the identifier and header routines in site-number order constructs
the specified memory image. The scan spends two probes per child and three
per output site. -/
theorem native_layer (L : Layer) (cap previous base : ℕ) (state : Word w)
    (priv : Word w → Word w) (counts starts : Fin L.count → Word w) (mem : Memory w)
    (hrow : ∀ i, rowRepresents mem (counts i) (starts i)
      ((L.ids i).map (fun j : ℕ => (j : Word w))))
    (countBefore : ∀ i, (counts i).val < base)
    (sourceBefore : ∀ i, (starts i).val + (L.ids i).length ≤ base)
    (hc : ∀ i, (L.ids i).length ≤ cap) (fit : endPos cap base L < 2 ^ w) :
    ∃ es, LayerPasses L cap previous base state priv counts starts (List.finRange L.count) mem es ∧
      after mem es = writeLayer cap previous base L mem ∧
      countProbes es = 2 * (∑ i, (L.ids i).length) + 3 * L.count := by
  classical
  let target := writeLayer cap previous base L mem
  have rows := writeLayer_rows cap previous base L mem hc fit
  have run (xs : List (Fin L.count)) (m : Memory w)
      (source : ∀ x < base, m x = mem x) :
      ∃ es, LayerPasses L cap previous base state priv counts starts xs m es ∧
        (∀ x, (∃ i ∈ xs, live L cap base i x) → after m es x = target x) ∧
        (∀ x, (∀ i ∈ xs, ¬ live L cap base i x) → after m es x = m x) ∧
        countProbes es = 2 * (xs.map (fun i => (L.ids i).length)).sum + 3 * xs.length := by
    induction xs generalizing m with
    | nil => exact ⟨[], .nil m, by simp, fun _ _ => rfl, by simp [countProbes]⟩
    | cons i xs ih =>
      let n := address cap base i.val
      let ids := (L.ids i).map (fun j : ℕ => (j : Word w))
      have hids : ids.length = (L.ids i).length := List.length_map _
      have lower : base ≤ n := Nat.le_add_right _ _
      have upper : n + (cap + 2) ≤ endPos cap base L := row_end_le _ _ _ _
      have capacity := hc i
      have represented : rowRepresents m (counts i) ((starts i).val : Word w) ids := by
        have start : ((starts i).val : Word w) = starts i :=
          Fin.ext (Nat.mod_eq_of_lt (starts i).isLt)
        rw [start]
        obtain ⟨hcount, hcells⟩ := hrow i
        refine ⟨(congrArg Fin.val (source _ (countBefore i))).trans hcount, fun j => ?_⟩
        have hj := Nat.add_lt_add_left (j.isLt.trans_eq hids) (starts i).val
        exact (source _ (hj.trans_le (sourceBefore i))).trans (hcells j)
      obtain ⟨ss, pass⟩ := DescriptorRows.native_pass Fin.elim0 state priv m n (starts i).val
        (n + 2) (counts i) (previous : Word w) ((cap + 2 : ℕ) : Word w) ids represented
        (by rw [hids]; have := sourceBefore i; omega) (by have := countBefore i; omega)
        (by omega) (by rw [hids]; omega)
      have skip (x : ℕ) (hx : ¬ live L cap base i x) : after m ss x = m x := pass_outside pass x hx
      have mid (x : ℕ) (hx : x < base) : after m ss x = mem x :=
        (skip x (fun live => hx.not_ge (lower.trans live.1))).trans (source x hx)
      have same (x : ℕ) (hx : live L cap base i x) : after m ss x = target x := by
        have exactRow : DFS.Row (after m ss) n (n + 2) (childWords w cap previous L i) :=
          (scanned_addresses L i cap previous) ▸ pass.row
        apply agree_row exactRow (rows i).2 x hx.1
        simpa only [childWords, List.length_map] using hx.2
      obtain ⟨es, tail, applied, outside, probes⟩ := ih (after m ss) mid
      have replay : after m (ss ++ es) = after (after m ss) es := List.foldl_append
      refine ⟨ss ++ es, .cons pass tail, ?_, ?_, ?_⟩
      · intro x h
        rw [replay]
        by_cases later : ∃ j ∈ xs, live L cap base j x
        · exact applied x later
        · rw [outside x (by simpa only [not_exists, not_and] using later)]
          obtain ⟨j, hj, hl⟩ := h
          rcases List.mem_cons.mp hj with rfl | hj
          · exact same _ hl
          · exact (later ⟨j, hj, hl⟩).elim
      · intro x h
        rw [replay, outside x (fun j hj => h j (List.mem_cons_of_mem _ hj))]
        exact skip x (h i List.mem_cons_self)
      · rw [append_probes, pass.probes, hids, probes, List.map_cons, List.sum_cons,
          List.length_cons]
        omega
  obtain ⟨es, runs, applied, outside, probes⟩ := run (List.finRange L.count) mem (fun _ _ => rfl)
  refine ⟨es, runs, ?_, ?_⟩
  · funext x
    by_cases h : ∃ i, live L cap base i x
    · obtain ⟨i, hi⟩ := h
      exact applied x ⟨i, List.mem_finRange _, hi⟩
    · rw [outside x (fun i _ hi => h ⟨i, hi⟩)]
      exact (writeLayer_unchanged cap previous base L mem x h).symm
  · simpa only [← List.ofFn_eq_map, List.sum_ofFn, List.length_finRange] using probes

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
