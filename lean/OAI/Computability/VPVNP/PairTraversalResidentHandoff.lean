import OAI.Computability.VPVNP.PairTerminalPrefixLinked
import OAI.Computability.VPVNP.PairTerminalPrefixBudget
import OAI.Computability.VPVNP.PairTerminalSelectedHeaders
import OAI.Computability.VPVNP.CompressorSelectedDirectoryHistory

/-!
# Traversal operands at the prefix-to-row boundary

The final prefix table is above all previous pass directories and the scalar
fields of the final level. The prefix worker changes the high-header total
and role offset, while the linker uses its phase and saved ordinal. This
separation preserves the chronological directories and supplies the operand
words to the first traversal call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalResidentHandoff

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles TraversalControllerInputs TerminalPrefix TerminalPrefix.Linked
open scoped Fin.CommRing

variable {w a g : ℕ}

/-- The scalar operands of every live pass end before the DFS arena. -/
theorem headers_before (L : Layout) {last : ℕ} (hl : last < L.levels)
    (wide : 28 ≤ L.shape.scalarFields) (j : ℕ) (hj : j ≤ last) :
    levelStart L 0 + j * levelWords L + 28 ≤ endAddress L := by
  have span : 28 ≤ levelWords L := by unfold levelWords levelHeaderWords; omega
  have next := levelStart_mono L (show j+1 ≤ L.levels by omega)
  simpa only [levelStart, Nat.succ_mul, Nat.zero_mul, Nat.add_zero, endAddress,
    Nat.add_assoc] using (Nat.add_le_add_left span (levelStart L j)).trans (by
      simpa only [levelStart, Nat.succ_mul, Nat.add_assoc] using next)

/-- Calendar cells strictly before the last scalar-header boundary are
retained. The remaining traversal operands have the values written by the
bootstrap or by the prefix worker's closing call. -/
structure Fields (L : Layout) (last : ℕ) (tab : Fin L.shape.tables) (A : TerminalBootstrap.Header L last)
    (cap H : ℕ) (Y : State a g) (pub : Fin 11 → Word w) (calendar out : Memory w) : Prop where
  head : terminalHead pub = (H : Word w)
  fits : H + 32 ≤ 2 ^ w
  levelFrame : ∀ x < levelStart L last + 28, out x = calendar x
  tableFrame : ∀ x < H, x < tableBase L last tab ∨ tableBase L last tab + arcCount Y ≤ x →
    out x = calendar x
  headerFields : ∀ i : Fin 21, 0 < i.val → i.val ≠ 12 → i.val ≠ 14 →
    out (H+i.val) = TerminalBootstrap.values L last A cap pub calendar i
  total : (out (H+12)).val = Y.totalWidth
  arenaFits : endAddress L ≤ H
  levelCountFit : last+1 < 2 ^ w
  finalSitesFit : Y.positions < 2 ^ w
  levels : out (H+1) = ((last+1 : ℕ) : Word w)
  sites : out (H+7) = (A.sites : Word w)
  offset : out (H+14) = ((A.rowWords cap + Y.totalWidth : ℕ) : Word w)
  stride : out (H+15) = ((cap+2 : ℕ) : Word w)
  first : out (H+16) = (levelStart L 0 : Word w)
  pitch : out (H+17) = (levelWords L : Word w)

/-- Read the operands from any memory agreeing with the standalone prefix
reports off the two linker control cells. The physical prefix exit satisfies
this agreement by `Start.handoff_rows`. -/
theorem fields_of_start (L : Layout) (last : ℕ) (hl : last < L.levels)
    (tab : Fin L.shape.tables) (A : TerminalBootstrap.Header L last) (limit r : ℕ)
    {workers : TerminalLink.Stage → LiveProgram.PairTable} {clock fuel : ℕ}
    (Y : State a g) (pub : Fin 11 → Word w) (calendar out : Memory w)
    (ready : TerminalBootstrap.Ready L last A pub calendar)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ L.base + 2 ^ r * 2 ^ r)
    (room : L.base + 2 ^ r * 2 ^ r ≤ 2 ^ w)
    (above : endAddress L ≤ TerminalBootstrap.address L.base r)
    (wide : 28 ≤ L.shape.scalarFields) (cells : arcCount Y ≤ tableWords L)
    (rs : List (Report w)) :
    let boot := TerminalBootstrap.report L.shape limit pub 0 calendar
    let dir := packedIncidence L w last (arcCount Y)
    Start workers pub clock fuel Y dir (tableBase L last tab) calendar boot rs →
    SourceTransport.Agree (TerminalLink.workerCell (TerminalLink.header pub))
      (after (after calendar boot.events) (eventLog rs)) out →
    Fields L last tab A limit (TerminalBootstrap.address L.base r) Y pub calendar out := by
  intro boot dir start agree
  let H := TerminalBootstrap.address L.base r
  let h := TerminalLink.header pub
  let src := after calendar boot.events
  let scan := after src (eventLog rs)
  let ptr := (tableBase L last tab : Word w)
  have hv : h.val = H := header_val L pub r ready.workspace exp hr reserve room
  have fits : H + 32 ≤ 2 ^ w := by dsimp only [H, TerminalBootstrap.address]; omega
  have pos (i : ℕ) (hi : i < 32) : (h + (i : Word w)).val = H + i := by
    rw [Fin.val_add, hv, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : i < 2 ^ w),
      Nat.mod_eq_of_lt (by omega)]
  have before := (tableEnd_le_nextLevel L last tab).trans ((levelStart_mono L hl).trans above)
  have ptrVal : ptr.val = tableBase L last tab := Nat.mod_eq_of_lt (by omega)
  have prefixEnd : ptr.val + arcCount Y ≤ H := by rw [ptrVal]; omega
  have saved : (h+31).val = H+31 := pos 31 (by decide)
  have data (x : ℕ) (x₀ : x ≠ H) (x₁ : x ≠ H+31) :
      TerminalLink.workerCell h x := by
    change x ≠ h.val ∧ x ≠ (h+31).val
    rwa [hv,saved,and_iff_right x₀]
  obtain ⟨_, _, stored, keep, _⟩ := TerminalBootstrap.native L last A limit pub calendar 0
    ready r exp hr reserve room
  have totalPos : (h+12).val = H+12 := pos 12 (by decide)
  have rolePos : (h+14).val = H+14 := pos 14 (by decide)
  have outside (x : ℕ) (h₁ : x ≠ H+12) (h₂ : x ≠ H+14)
      (hx : x < ptr.val ∨ ptr.val + arcCount Y ≤ x) : scan x = src x := by
    have frame := start.rawScan.stored.outside x (totalPos ▸ h₁) hx
    change scan x = writeMemory src (h+14) _ x at frame
    simpa only [writeMemory, rolePos, ite_eq_right h₂] using frame
  have read (i : Fin 21) (hi : 0 < i.val) (ht : i.val ≠ 12) (hr : i.val ≠ 14) :
      out (H+i.val) = TerminalBootstrap.values L last A limit pub calendar i := by
    have small := i.isLt
    exact (agree _ (data _ (by omega) (by omega))).symm.trans
      ((outside _ (by omega) (by omega) (.inr (by omega))).trans (stored i))
  have low : levelStart L last + 28 ≤ ptr.val := by
    rw [ptrVal]
    unfold tableBase arrayBase incidenceStart levelHeaderWords
    omega
  have head : terminalHead pub = (H : Word w) := by
    simpa only [ready.workspace,exp,H,TerminalBootstrap.address] using
      terminalHead_eq_nat pub (exp ▸ hr) (by rwa [ready.workspace,exp])
  have pitchPos : 0 < levelWords L := by unfold levelWords levelHeaderWords; omega
  have bound : last+1 ≤ endAddress L := by
    apply (Nat.le_mul_of_pos_right (last+1) pitchPos).trans
    exact (Nat.le_add_left ..).trans (levelStart_mono L hl)
  have sitesLe : Y.positions ≤ arcCount Y := by
    rw [Segment.arc_count_positions]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have frame (x : ℕ) (hx : x < H) (ht : x < ptr.val ∨ ptr.val + arcCount Y ≤ x) :
      out x = calendar x :=
    (agree _ (data _ (by omega) (by omega))).symm.trans
      ((outside x (by omega) (by omega) ht).trans (keep x (.inl hx)))
  refine ⟨head, fits, ?_, ?_, read, ?_, above, by omega, by omega,
    read 1 (by decide) (by decide) (by decide), read 7 (by decide) (by decide) (by decide), ?_,
    read 15 (by decide) (by decide) (by decide), read 16 (by decide) (by decide) (by decide),
    read 17 (by decide) (by decide) (by decide)⟩
  · intro x hx
    have below := hx.trans_le low
    exact frame x (by omega) (.inl below)
  · simpa only [ptrVal] using frame
  · exact (congrArg Fin.val (agree _ (data (H+12) (by omega) (by omega))).symm).trans
      (totalPos ▸ start.rawScan.stored.total)
  · have role := start.rawScan.role
    change scan (h+14).val = src (h+5).val + (Y.totalWidth : Word w) at role
    rw [rolePos, show (h+5).val = H+5 from pos 5 (by decide),
      show src (H+5) = (A.rowWords limit : Word w) from stored 5] at role
    exact (agree _ (data _ (by omega) (by omega))).symm.trans (role.trans (Nat.cast_add ..).symm)

open LocalHistory SelectedDirectoryHistory

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)
local notation "vs" => executeLevels B f hf T hT X z
local notation "ls" => selectedLayers B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

/-- The same directories that were produced by the selected pass executions
supply the traversal workers on the prefix exit memory. -/
theorem selected_resident (L : Layout) (baseBits laneBits : ℕ) (tab : Fin L.shape.tables)
    {H : ℕ} {pub : Fin 11 → Word w} {calendar out : Memory w}
    (D : Retained B f hf T hT X z L (endAddress L) calendar)
    (fields : Fields L (ls).dropLast.length tab
      (TerminalBootstrap.fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab)
      B.recordLimit H (Y) pub calendar out)
    (hl : (ls).dropLast.length < L.levels) (wide : 28 ≤ L.shape.scalarFields) :
    ∃ ds : (i : Fin (vs).length) → LevelDirectory vs[i] out (endAddress L),
      (∀ i, (ds i).pub = (D.dirs i).pub) ∧
      Resident pub out H (levelStart L 0) (levelWords L)
        (words B.recordLimit (ls) + (Y).totalWidth) B.recordLimit (endAddress L)
        ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers (vs) ds) ∧
      ∀ j ≤ (vs).length, levelStart L 0 + j * levelWords L + 28 ≤ endAddress L := by
  have last : (ls).dropLast.length = (vs).length := by
    simp only [List.length_dropLast, selectedLayers_eq_levels, List.length_cons, List.length_map,
      Nat.add_sub_cancel]
  let kept := D.transport (raw' := out) (fun x _ hx => fields.levelFrame x (last ▸ hx))
  have before (j : ℕ) (hj : j ≤ (vs).length) :=
    headers_before L hl wide j (last ▸ hj)
  have count : (out (H+1)).val = (vs).length+1 := by
    rw [fields.levels, Fin.val_natCast, Nat.mod_eq_of_lt fields.levelCountFit, last]
  have off := fields.offset
  rw [TerminalBootstrap.selected_rowWords] at off
  have addr (j : ℕ) : levelStart L 0 + j * levelWords L = levelStart L j := by
    simp [levelStart]
  refine ⟨kept.dirs,fun _ => rfl,?_,before⟩
  apply selected_resident_of_directory_fields B f hf T hT X z (endAddress L) out kept.dirs
    fields.head fields.fits fields.first fields.pitch off fields.stride count
  · intro j hj
    have bound := before j hj
    have fh := fields.fits
    have lower := fields.arenaFits
    omega
  · intro j hj
    rw [addr]
    exact kept.current j hj
  · intro j
    rw [addr]
    exact kept.role j
  · intro i hi
    simpa only [hi] using kept.old i
  · intro empty
    have sizes := (TerminalBootstrap.selected_counts B f hf T hT X z).symm.trans
      (selected_layer_counts B f hf T hT X z)
    have same : (Y).positions = X.positions := by simpa only [empty, List.map_nil, List.nil_append,
      List.cons.injEq, and_true] using sizes
    rw [fields.sites, TerminalBootstrap.fromState_sites, Fin.val_natCast,
      Nat.mod_eq_of_lt fields.finalSitesFit, same]
  · intro i
    rw [addr]
    exact kept.directory i

/-- The physical entry to traversal-row construction has exactly the operand
banks of the selected calendar. The calendar's online control words may have
changed between the raw pass run and the terminal bootstrap. -/
theorem selected_physical (L : Layout) (baseBits laneBits : ℕ) (tab : Fin L.shape.tables)
    {workers : TerminalLink.Stage → LiveProgram.PairTable} {clock fuel : ℕ}
    (r : ℕ) (pub : Fin 11 → Word w) (raw calendar : Memory w)
    (D : Retained B f hf T hT X z L (endAddress L) raw)
    (online : SourceTransport.Agree (levelStart L 0 ≤ ·) raw calendar)
    (size : L.levels = T * (S.steps + 1) + 1) (wide : 28 ≤ L.shape.scalarFields)
    (ready : TerminalBootstrap.Ready L (ls).dropLast.length
      (TerminalBootstrap.fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab) pub calendar)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ L.base + 2 ^ r * 2 ^ r)
    (room : L.base + 2 ^ r * 2 ^ r ≤ 2 ^ w)
    (above : endAddress L ≤ TerminalBootstrap.address L.base r)
    (cells : arcCount (Y) ≤ tableWords L) (rs : List (Report w)) :
    let last := (ls).dropLast.length
    let boot := TerminalBootstrap.report L.shape B.recordLimit pub 0 calendar
    let dir := packedIncidence L w last (arcCount (Y))
    let out := prefixMemory pub calendar boot rs
    Start workers pub clock fuel (Y) dir (tableBase L last tab) calendar boot rs →
    ∃ ds : (i : Fin (vs).length) → LevelDirectory vs[i] out (endAddress L),
      (∀ i, (ds i).pub = (D.dirs i).pub) ∧
      Resident pub out (TerminalBootstrap.address L.base r) (levelStart L 0) (levelWords L)
        (words B.recordLimit (ls) + (Y).totalWidth) B.recordLimit (endAddress L)
        ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers (vs) ds) ∧
      ∀ j ≤ (vs).length, levelStart L 0 + j * levelWords L + 28 ≤ endAddress L := by
  intro last boot dir out start
  have hl : last < L.levels := by
    change (ls).dropLast.length < L.levels
    rw [TerminalBootstrap.selected_prior_length, size]
    omega
  let dc := D.transport (raw' := calendar) (fun x hx _ =>
    (online x (by simpa only [levelStart,Nat.zero_mul,Nat.add_zero] using hx)).symm)
  have h := fields_of_start L last hl tab _ B.recordLimit r (Y) pub calendar out ready
    exp hr reserve room above wide cells rs start start.handoff_rows.1
  exact selected_resident B f hf T hT X z L baseBits laneBits tab dc h hl wide

end PairSimulation.TraversalResidentHandoff

end VPVNP
end Computability
end OAI
