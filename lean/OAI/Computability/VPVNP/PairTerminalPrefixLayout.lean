import OAI.Computability.VPVNP.PairTerminalPrefixSegment
import OAI.Computability.VPVNP.PairTraversalTerminalBootstrap

/-!
# Terminal width scan in the actual descriptor workspace

The last reserved level's packed width column precedes its prefix table.
The high header contains the total and role offset, above every live table.
The terminal bootstrap supplies the scan's operands and zero accumulator
while preserving the actual incidence columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DescriptorSpace
open scoped Fin.CommRing

variable {w a g : ℕ}

open private eval_high from OAI.Computability.VPVNP.PairTraversalTerminalBootstrap

/-- The master link and the terminal bootstrap compute the same high header. -/
theorem header_val (L : Layout) (pub : Fin 11 → Word w) (r : ℕ)
    (workspace : (pub 2).val = L.base) (exp : (pub 7).val = r) (hr : r < w)
    (reserve : 32 ≤ L.base + 2 ^ r * 2 ^ r) (room : L.base + 2 ^ r * 2 ^ r ≤ 2 ^ w) :
    (Worker.header pub).val = TerminalBootstrap.address L.base r := by
  have h : Worker.header pub = (TerminalBootstrap.address L.base r : Word w) :=
    eval_high L pub (fun _ => 0) workspace 0 (by omega) r exp hr reserve
  rw [h, Fin.val_natCast, Nat.mod_eq_of_lt]
  unfold TerminalBootstrap.address
  omega

/-- The prefix table and high accumulator obey both the scalar scan's range
conditions and the terminal worker's header separation conditions. -/
theorem packed_layout (L : Layout) (last : Fin L.levels) (tab : Fin L.shape.tables)
    (pub : Fin 11 → Word w) (n : ℕ) (cap : n ≤ slotCapacity L) (cells : n ≤ tableWords L)
    (above : endAddress L ≤ (Worker.header pub).val)
    (room : (Worker.header pub).val + 15 ≤ 2 ^ w) :
    let T := packedIncidence L w last n
    let start := (tableBase L last tab : Word w)
    Segment.HeaderLayout pub T start n ∧
      SliceRAM.PrefixRegions (operands T start (Worker.header pub + 12)) n := by
  let H := (Worker.header pub).val
  have ht := (Nat.add_le_add_left cells (tableBase L last tab)).trans
    ((tableEnd_le_nextLevel L last tab).trans ((levelStart_mono L last.isLt).trans above))
  obtain ⟨hw, _, hf⟩ := prefix_bounds L (w := w) last tab n H cap cells above (by omega)
  have hp : (tableBase L last tab : Word w).val = tableBase L last tab :=
    Nat.mod_eq_of_lt (by omega)
  have htotal : (Worker.header pub + 12).val = H + 12 := by
    change (H + 12 % (2 ^ w)) % (2 ^ w) = _
    rw [Nat.mod_eq_of_lt (by omega : 12 < 2 ^ w), Nat.mod_eq_of_lt (by omega)]
  have s : Segment.HeaderLayout pub (packedIncidence L w last n) (tableBase L last tab) n :=
    ⟨room, Or.inl (by rw [hp]; exact ht), Or.inl (hw.trans ((Nat.le_add_right _ _).trans ht))⟩
  refine ⟨s, ?_⟩
  change SliceRAM.PrefixRegions ![_, (tableBase L last tab : Word w), Worker.header pub + 12] n
  refine ⟨(hw.trans (Nat.le_add_right _ _)).trans hf.le, ?_, Or.inl ?_, Or.inr ?_, Or.inr ?_⟩
  · change (tableBase L last tab : Word w).val + n ≤ _
    rw [hp]
    exact hf.le
  · change _ ≤ (tableBase L last tab : Word w).val
    rw [hp]
    exact hw
  · change _ ≤ (Worker.header pub + 12).val
    rw [htotal]
    exact (hw.trans ((Nat.le_add_right _ _).trans ht)).trans (Nat.le_add_right _ _)
  · change (tableBase L last tab : Word w).val + n ≤ (Worker.header pub + 12).val
    rw [hp, htotal]
    exact ht.trans (Nat.le_add_right _ _)

open private incidence_end_le from OAI.Computability.VPVNP.CompressorDescriptorSpace

private theorem transfer_incidence (L : Layout) (last : Fin L.levels) (X : State a g)
    (n : ℕ) (hn : n = arcCount X) (cap : n ≤ slotCapacity L) {H : ℕ}
    (above : endAddress L ≤ H) (room : H < 2 ^ w) {m m' : Memory w}
    (old : (packedIncidence L w last n).ActualColumns X m)
    (before : ∀ x < H, m' x = m x) : (packedIncidence L w last n).ActualColumns X m' := by
  let T := packedIncidence L w last n
  have port (c : Fin 6) (e : X.network.Edge) :
      (T.column c + IncidenceDirectory.actualPort X e).val < H := by
    let i := (LocalHistory.edgeOrder X).entries.symm e
    have index : i.val < n := hn ▸ i.isLt
    have bounds := (incidence_bounds L last n cap c ⟨i.val, index⟩).2
    have endLe : arrayBase L last ≤ endAddress L :=
      (incidence_end_le L last).trans (levelStart_mono L last.isLt)
    have small : incidenceBase L last n c + i.val < H := bounds.trans_le (endLe.trans above)
    rw [packed_column, actualPort_eq]
    change (incidenceBase L last n c % (2 ^ w) + i.val % (2 ^ w)) % (2 ^ w) < H
    rw [Nat.mod_eq_of_lt (by omega : incidenceBase L last n c < 2 ^ w),
      Nat.mod_eq_of_lt (by omega : i.val < 2 ^ w), Nat.mod_eq_of_lt (small.trans room)]
    exact small
  exact ⟨fun e => (before _ (port 3 e)).trans (old.actualOut e),
    fun e => (before _ (port 4 e)).trans (old.actualIn e),
    fun e => (before _ (port 5 e)).trans (old.width e)⟩

/-- Run the terminal bootstrap followed by the complete prefix worker stage on
the same selected final state. The role offset and bit width are the actual
traversal storage size and total width of that state. -/
theorem run_after_bootstrap (L : Layout) (last : Fin L.levels) (tab : Fin L.shape.tables)
    (A : TerminalBootstrap.Header L last) (cap r : ℕ) (pub : Fin 11 → Word w)
    (s : Word w) (m : Memory w) (X : State a g)
    (ready : TerminalBootstrap.Ready L last A pub m)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ L.base + 2 ^ r * 2 ^ r)
    (room : L.base + 2 ^ r * 2 ^ r ≤ 2 ^ w)
    (above : endAddress L ≤ TerminalBootstrap.address L.base r)
    (nslots : A.sites * A.degree = arcCount X)
    (wh : A.widthHead = incidenceBase L last (arcCount X) 5)
    (sh : A.prefixBase = tableBase L last tab) (slots : arcCount X ≤ slotCapacity L)
    (cells : arcCount X ≤ tableWords L) (totalFit : X.totalWidth < 2 ^ w)
    (incidence : (packedIncidence L w last (arcCount X)).ActualColumns X m) :
    let M := (TerminalBootstrap.table L.shape cap).instantiate w pub
    let rep := TerminalBootstrap.report L.shape cap pub s m
    let boot := after m rep.events
    let T := packedIncidence L w last (arcCount X)
    execute M.program (TerminalBootstrap.cost L.shape cap + 1) (M.program.start s) m [] =
      some rep ∧ ∃ rs, Segment.Run pub X T (tableBase L last tab) boot rs ∧
        after boot (eventLog rs) (Worker.header pub + 14).val =
          ((A.rowWords cap + X.totalWidth : ℕ) : Word w) := by
  let H := TerminalBootstrap.address L.base r
  let boot := after m (TerminalBootstrap.report L.shape cap pub s m).events
  have hv := header_val L pub r ready.workspace exp hr reserve room
  have high : H + 32 ≤ 2 ^ w := by dsimp [H, TerminalBootstrap.address]; omega
  obtain ⟨run, _, header, keep, _⟩ := TerminalBootstrap.native L last A cap pub m s
    ready r exp hr reserve room
  have fields (j : Fin 21) : boot (Worker.header pub + (j.val : Word w)).val =
      TerminalBootstrap.values L last A cap pub m j := by
    have hj := j.isLt
    rw [Fin.val_add, hv, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : j.val < 2 ^ w),
      Nat.mod_eq_of_lt (by change H + j.val < 2 ^ w; omega)]
    exact header j
  obtain ⟨layout, regions⟩ := packed_layout L last tab pub (arcCount X) slots cells
    (hv ▸ above) (by rw [hv]; change H + 15 ≤ 2 ^ w; omega)
  have rep := transfer_incidence L last X (arcCount X) rfl slots above
    (by change H < 2 ^ w; omega) incidence (fun x hx => keep x (Or.inl hx))
  have fit : arcCount X < 2 ^ w := by
    have hb := regions.startsFit
    have hh := layout.startsApart
    rcases hh with hh | hh
    · have hhead := layout.fits
      omega
    · have hhead := layout.fits
      change (tableBase L last tab : Word w).val + arcCount X ≤ 2 ^ w at hb
      omega
  obtain ⟨rs, scan⟩ := Segment.run pub X _ (tableBase L last tab) boot rep layout regions fit
    totalFit ((fields 8).trans (congrArg (fun n : ℕ => (n : Word w)) nslots))
    ((fields 9).trans (congrArg (fun n : ℕ => (n : Word w)) wh))
    ((fields 11).trans (congrArg (fun n : ℕ => (n : Word w)) sh)) (fields 12)
  refine ⟨run, rs, scan, ?_⟩
  exact scan.role.trans (by
    unfold Segment.roleValue
    rw [show boot (Worker.header pub + 5).val = (A.rowWords cap : Word w) from fields 5]
    simp only [Nat.cast_add])

end PairSimulation.TerminalPrefix

end VPVNP
end Computability
end OAI
