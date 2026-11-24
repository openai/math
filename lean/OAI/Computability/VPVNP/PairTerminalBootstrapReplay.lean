import OAI.Computability.VPVNP.PairTerminalQuietFrame

/-!
# Packed addresses in the first two terminal phases

The 21 bootstrap stores, width column, prefix table and linked control cells
all lie at or above the workspace base. This supplies the protected-address
frame of those stages even on a terminal run with a rejecting suffix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM Compression CompressorRecords DescriptorSpace TerminalPrefix TerminalPrefix.Linked
open scoped Fin.CommRing

variable {w a g : ℕ} {workers : Stage → LiveProgram.PairTable} {pub : Fin 11 → Word w}

/-- Discharge all source and linker address conditions for the first two
stages from the actual packed layout and bootstrap data. -/
theorem QuietPrefix.replayFrame_packedStart
    (L : Layout) (last : Fin L.levels) (tab : Fin L.shape.tables)
    (hdr : TerminalBootstrap.Header L last) (limit r cap : ℕ)
    (X : State a g) (input : Memory w) (rs : List (Report w))
    (ready : TerminalBootstrap.Ready L last hdr pub input)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ L.base + 2 ^ r * 2 ^ r)
    (room : L.base + 2 ^ r * 2 ^ r ≤ 2 ^ w)
    (above : endAddress L ≤ TerminalBootstrap.address L.base r)
    (slots : arcCount X ≤ slotCapacity L)
    (q : QuietPrefix workers pub cap input)
    (start : Start workers pub cap (TerminalBootstrap.cost L.shape limit + 1) X
      (packedIncidence L w last (arcCount X)) (tableBase L last tab) input
      (TerminalBootstrap.report L.shape limit pub 0 input) rs)
    (clock₀ : TerminalBootstrap.cost L.shape limit + 1 + 30 ≤ cap) (clock₁ : 60 ≤ cap)
    (x : ℕ) (hx : x < L.base)
    (third : ReplayFrame x q.prefixRows.val.memory
      (reports (header pub) q.traversalRows.val.logs)) : ReplayFrame x input q.reportList := by
  let H := TerminalBootstrap.address L.base r
  have hhead : (header pub).val = H :=
    header_val L pub r ready.workspace exp hr reserve room
  have fits : H + 32 ≤ 2 ^ w := by unfold H TerminalBootstrap.address; omega
  have xbase : L.base ≤ endAddress L := by
    simp only [endAddress,levelStart,levelsBase,directoryBase,plannerTag,frameBase]
    omega
  have low : x < H := hx.trans_le (xbase.trans above)
  have saved : (header pub + 31).val = H + 31 := by
    rw [Fin.val_add,hhead,show (31 : Word w).val = 31 % (2 ^ w) from rfl,
      Nat.mod_eq_of_lt (by omega : 31 < 2 ^ w),Nat.mod_eq_of_lt (by omega)]
  have away : workerCell (header pub) x := ⟨hhead ▸ low.ne,by omega⟩
  have outside := (TerminalBootstrap.native L last hdr limit pub input 0 ready r exp hr
    reserve room).2.2.2.1
  apply q.replayFrame_of_start start clock₀ clock₁ x away (outside x (.inl low)) _ third
  have fit : endAddress L < 2 ^ w := above.trans_lt (by omega)
  have widthEnd := packed_incidence_room L fit last slots
  have startsEnd := (tableEnd_le_nextLevel L last tab).trans (levelStart_mono L last.isLt)
  have widthFit : incidenceBase L last (arcCount X) 5 < 2 ^ w := by
    change incidenceStart L last + 5 * arcCount X < 2 ^ w
    omega
  change tableBase L last tab + tableWords L ≤ endAddress L at startsEnd
  have startsFit : tableBase L last tab < 2 ^ w := by omega
  have widths : (packedIncidence L w last (arcCount X)).width.val =
      incidenceBase L last (arcCount X) 5 := Nat.mod_eq_of_lt widthFit
  have starts : (tableBase L last tab : Word w).val = tableBase L last tab :=
    Nat.mod_eq_of_lt startsFit
  unfold Segment.probeRegion
  rw [show (Worker.header pub).val = H from hhead,widths,starts]
  simp only [tableBase,arrayBase,incidenceBase,incidenceStart,levelStart,
    levelsBase,directoryBase,plannerTag,frameBase]
  omega

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
