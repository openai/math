import OAI.Hierarchy.DescentTerminalPlacedHeaderColumns
import OAI.Hierarchy.DescentTerminalPlacedChipInit

namespace OAI
/-! # The physical row and literal arrays at both header instructions -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitter DescentTerminalRowArena
open DescentTerminalPaidHeaderEvents DescentTerminalHeaderDraft DescentTerminalVertexFields
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8000

variable {blocks v B w : ℕ} (V : Home.Format) (S : DescentTerminalCompiledPrefix.Shape)
    (I : Input) (R : MaskAllocation.Channels blocks) (start head : ℕ)
    (short : v*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ B)
    (literal : Compact.Literals I.sources)
local notation "C_" => meter V R start
local notation "O_" => registers V S R start head
local notation "base_" => afterMeter V S R start
local notation "A_" => rowArena S I base_
local notation "L_" => layout S I base_ O_
local notation "E_" => emitter S I base_
local notation "load_" => input V S I R start head short literal
local notation "μ" m => Suffix.events S L_ (C_).layout ((A_).mount (load_ m))

def phase (m : Memory w) (fmt : Bool) : Memory w :=
  if fmt then indexed S.terminal E_ (μ m) else external S.terminal E_ (μ m)

variable (m : Memory w) (early : Earlier S I (afterMeter V S R start) (meter V R start).layout w) (room : last V S I R start < 2^w)
local notation "atPhase" => phase (w:=w) V S I R start head short literal

include early room in
theorem low_phase (fmt : Bool) (x : ℕ) (low : x < (A_).start+2) :
    atPhase m fmt x=(A_).mount (load_ m) x := by
  have ready := suffix_room S I base_ (C_).layout O_ early room
  have saved := before S I base_ O_ x low
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I base_
  have origin : x<takeOff S I base_ := saved.page.trans_le (p0.trans p1)
  have one : BeforeKey S.terminal E_ x := by
    constructor <;> change x<takeOff S I base_+_ <;> omega
  have two := after_start S I base_ O_ (a:=x) (by change x<takeOff S I base_+_; omega)
  have names : AfterNames E_ x :=
    ⟨two.later.names,two.later.progress,two.later.gates,two.later.leaves,two.later.scalar⟩
  have lastWord := printed_before S.terminal E_ (μ m) ready.issuer one two
  have mid := (after_index S.terminal E_ (μ m) ready.issuer names two.later.formats).symm.trans lastWord
  have firstWord := (Header.early (E_).indices (external S.terminal E_ (μ m))
    ready.issuer.idx two.later.indices).symm.trans mid
  have across := Suffix.early S L_ (C_).layout ((A_).mount (load_ m)) ready saved.original saved.slot saved.page
  cases fmt
  · exact firstWord.trans across
  · exact mid.trans across

include early room in
theorem low_input (fmt : Bool) (x : ℕ) (low : x<start) : atPhase m fmt x=m x := by
  have bound : start≤base_ := by change start ≤ start+_+_+_+_+3; omega
  have hx : x < (A_).start := low.trans_le bound
  exact (low_phase V S I R start head short literal m early room fmt x (by omega)).trans
    (((A_).mount_before _ hx).trans (input_frame V S I R start head short literal m (.inl low)))

include early room in
theorem lane_words (fmt : Bool) (j : Fin 2) : atPhase m fmt ((A_).start+j.val)=(j.val:Word w) := by
  have hj := j.isLt
  have hs := S.sites_pos
  rw [low_phase V S I R start head short literal m early room fmt _ (by omega)]
  simpa only [Nat.mod_eq_of_lt hj, Arena.atBand, Nat.zero_mul, Nat.add_zero] using
    (A_).mount_low (load_ m) (i:=j.val) (by change j.val<2*S.sites;omega)

variable (priorArena : Arena) (sockets : DescentTerminalHeaderSockets.Layout) (degree n litBase : ℕ)
variable (priorRoom : DescentTerminalHeaderDraft.Room priorArena sockets degree w)
local notation "boot_" => litMem litBase n m
local notation "source_" => data priorArena sockets degree boot_

include early room priorRoom in
/-- The preceding three native event arrays survive every scalar instruction and
both width scans. Literal values come from the four actual contiguous ROMs loaded
before the draft; the one-bit operand comes from the row allocator at the later date. -/
theorem prepared (pos : 0<w) (placed : stop priorArena ≤ start)
    (litLow : litBase+4*DescentTerminalHeaderDraft.span n ≤ priorArena.start)
    (fmt : Bool) :
    (fixed (literals litBase n) S I base_).Reads (atPhase source_ fmt) n ∧
      ∀x<stop priorArena, atPhase source_ fmt x=source_ x := by
  have lp := priorArena.start_le 22
  have hi := priorRoom.area
  have fit : litBase+4*DescentTerminalHeaderDraft.span n<2^w :=
    litLow.trans_lt (lp.trans_lt (by
      have final : priorArena.finish≤ stop priorArena := by
        unfold DescentTerminalHeaderDraft.stop
        omega
      exact final.trans_lt hi))
  have keep (x : ℕ) (hx : x<stop priorArena) : atPhase source_ fmt x=source_ x :=
    low_input V S I R start head short literal _ early room fmt x (hx.trans_le placed)
  have lit := literal_reads_later litBase n m (atPhase source_ fmt) fit (by
    intro j hj
    have hsmall := hj.trans_le litLow
    have end_ : priorArena.finish≤ stop priorArena := Nat.le_add_right _ _
    exact (keep j ((hsmall.trans_le lp).trans_le end_)).trans
      (lowFrame priorArena sockets degree boot_ priorRoom j hsmall))
  exact ⟨⟨lit.halfRead,Allocation.parity_read _ _ pos
    (lane_words V S I R start head short literal source_ early room fmt),lit.direct,lit.blank⟩,keep⟩

include early room priorRoom in
/-- Only the literal and event intervals are read after the exterior reel has
moved the matrix and written the history counter in its own scratch interval. -/
theorem prepared_after (pos : 0<w) (placed : stop priorArena≤ start)
    (litLow : litBase+4*DescentTerminalHeaderDraft.span n≤priorArena.start)
    (later : Memory w) (recorded : ∀j,litBase≤j→j<stop priorArena→later j=source_ j)
    (fmt : Bool) :
    (fixed (literals litBase n) S I base_).Reads (atPhase later fmt) n ∧
      ∀j,priorArena.finish≤j→j<stop priorArena→atPhase later fmt j=source_ j := by
  have floor_ : litBase≤priorArena.start := (Nat.le_add_right ..).trans litLow
  have baseRoom := arenaFit priorArena sockets degree priorRoom
  have endRoom := priorArena.start_le 22
  have terminal : priorArena.finish≤ stop priorArena := Nat.le_add_right ..
  have keep (j : ℕ) (lo : litBase≤j) (hi : j<stop priorArena) :
      atPhase later fmt j=source_ j :=
    (low_input V S I R start head short literal later early room fmt j (hi.trans_le placed)).trans (recorded j lo hi)
  have ls := literal_reads_window litBase n m (atPhase later fmt)
    (litLow.trans_lt (endRoom.trans_lt baseRoom)) (fun j lo hj=> by
      have before := hj.trans_le litLow
      exact (keep j lo (before.trans_le (endRoom.trans terminal))).trans
        (lowFrame priorArena sockets degree boot_ priorRoom j before))
  exact ⟨⟨ls.halfRead,Allocation.parity_read _ _ pos
    (lane_words V S I R start head short literal later early room fmt),ls.direct,ls.blank⟩,
      fun j lo hi=>keep j (floor_.trans (endRoom.trans lo)) hi⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
