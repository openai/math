import OAI.Hierarchy.ProbeFixedWideFunded
import OAI.Hierarchy.TaggedWireWideLanguage
import OAI.Hierarchy.ProbeFixedWidePrivateHeader
import OAI.Hierarchy.ProbeFixedReadbackProducer

namespace OAI
/-! # Installing original selector words on the funded terminal tape -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets CatalystArchive
open Tagged WireTelescope StripChart
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "B" => v.nativeBoards P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "stock" => v.fixedTerminalStock P h width
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
variable (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "L" => (reader).format.windows
local notation "es" => events v.mesh

theorem wide_funded_raw_header (bits : ℕ) (raw : Bits (CalendarTape.bits (reader).format.slot es))
    (seed : Boot.Tape h D) :
    v.wideFundedRaw h width bits ((L).header es raw seed)=(L).header es raw (v.wideFundedRaw h width bits seed) := by
  let ss:=v.widePaidSlices h width bits
  let high:=v.wideRoleStart h width stock ss
  let occ:=v.catalystPairOwners P h width
  let par:=v.catalystPairParity P h width
  have point : AdviceLocal (v.wideFundedRaw h width bits) :=
    (show AdviceLocal (v.wideRoleWords h width stock ss) from v.role_cell h width stock ss).comp
      (show AdviceLocal (v.widePairedWords h width) from v.paired_cell h width)
  apply (L).header_local _ point es raw seed
  intro mem e active x hit
  have lower : (A).first ≤ x := by
    cases e with
    | attempt a => exact (Nat.le_add_right ..).trans (show (A).base v.mesh (.attempt a)≤x from hit.1)
    | feed b => have no : x<0:=hit.2; omega
  have upper : x < (A).endAddress v.mesh := by
    cases e with
    | feed b => have no : x<0:=hit.2; omega
    | attempt a =>
      have span : (L).cells (.attempt a) ≤ Slab.selectorSpan B := (reader).fits a
      have allocated : Slab.selectorSpan B ≤ (A).stride := by
        change Slab.selectorSpan B ≤ Slab.stride (v.slab (v.seed P h width) P width) B
        simp only [Slab.stride,PostLayout.column,PostLayout.startColumns,Slab.mask,Slab.flags,Slab.first,
          Nat.zero_add,Nat.add_assoc]
        exact Nat.le_add_right ..
      have last := (A).within v.mesh (.attempt a) active
      have position : x<(A).base v.mesh (.attempt a)+(L).cells (.attempt a) := hit.2
      omega
  change v.wideRoleWords h width stock ss (v.widePairedWords h width mem) x=mem x
  rw [show v.wideRoleWords h width stock ss (v.widePairedWords h width mem) x=
      v.widePairedWords h width mem x from RoleRoom.stocks_below v.sampler (v.wideOrder h width) directory
        (P).catalogue.rows high x (v.widePairedWords h width mem) (upper.trans_le (le_max_left ..))]
  have early : v.catalystStaticStart P h width≤(A).first:=v.catalyst_static_before P h width
  have pair:=v.paid_pair_ends P h width
  have span : 2*r≤occ.size := (Nat.lt_log2_self (n:=2*r)).le
  have tagSpan : 2*r≤par.size := (Nat.lt_log2_self (n:=2*r)).le
  have left : occ.base+occ.size≤(A).first:=pair.1.trans early
  have right : par.base+par.size≤(A).first:=pair.2.trans early
  apply PaidPairDirectory.frame occ par r
  rintro (⟨_,hi⟩|⟨_,hi⟩) <;> omega

/-- The funded execution accepts exactly the private tape of one
chronological histogram path on that same funded origin. -/
theorem wide_funded_admission (bits size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (seed : Boot.Tape h D) (raw : Bits (CalendarTape.bits (reader).format.slot es)) :
    let ord:=wideRouteOrder h D k
    let origin:=v.wideSignedMidAt h width size stock M π ord (v.wideFundedRaw h width bits seed)
    let tape:=v.wideFundedRaw h width bits ((L).header es raw seed)
    v.wideSignedCheckoutAt h width size stock M π ord tape ((A).endAddress v.mesh)=0 ↔
      ∃! j : CalendarTape.Path (reader).format.slot es origin,CalendarTape.encode (reader).format.slot es origin j=raw := by
  intro ord origin tape
  have verdict :
      v.wideSignedCheckoutAt h width size stock M π ord tape ((A).endAddress v.mesh)=0 ↔
        admissible (v.wideSignedChart h width stock) es (v.wideSignedMidAt h width size stock M π ord tape) :=
    v.wide_verdict h width size extent M π tape age budget small
  apply verdict.trans
  let accepts : Boot.Tape h D → Prop := fun input =>
    admissible (v.wideSignedChart h width stock) es (v.wideSignedMidAt h width size stock M π ord input)
  have header := congrArg accepts (v.wide_funded_raw_header h width age budget small bits raw seed)
  exact (Iff.of_eq header).trans
    (v.wide_tape_admission h width size extent M π (v.wideFundedRaw h width bits seed) age budget small raw)

theorem wide_funded_path (bits size : ℕ) (extent : (A).endAddress v.mesh ≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (seed : Boot.Tape h D) :
    let ord:=wideRouteOrder h D k
    let origin:=v.wideSignedMidAt h width size stock M π ord (v.wideFundedRaw h width bits seed)
    ∀j : CalendarTape.Path (reader).format.slot es origin,
      let word:=CalendarTape.encode (reader).format.slot es origin j
      v.wideSignedCheckoutAt h width size stock M π ord (v.wideFundedRaw h width bits ((L).header es word seed))
        ((A).endAddress v.mesh)=0 := by
  intro ord origin j word
  apply (v.wide_funded_admission h width age budget small bits size extent M π seed word).2
  exact ⟨j,rfl,fun _ same => (CalendarTape.encode (reader).format.slot es origin).injective same⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
