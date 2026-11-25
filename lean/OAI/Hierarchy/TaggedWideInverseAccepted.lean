import OAI.Hierarchy.TaggedWideOriginalHeader
import OAI.Hierarchy.TaggedWideFundedGateRoom
import OAI.Hierarchy.ProbeFixedWideCountedParents
import OAI.Hierarchy.TaggedWideCountedAdmission

namespace OAI
/-! # Running the funded signed calendar from the external parent permutation -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory AdaptiveProbe ProbeStage CoreBoard CoreRoute
open Tagged Tagged.WideControlJoin WireTelescope StripChart CatalystArchive
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "V" => v.catalystMarkets P h width
local notation "W" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "o" => wideRouteOrder h D k
local notation "es" => events v.mesh
local notation "flag" => (A).endAddress v.mesh
local notation "L" => (v.wideSelector h width age budget small).format.windows
local notation "slot" => (v.wideSelector h width age budget small).format.slot

variable (S : ℕ) (highSeed : Boot.Tape h (2^v.W)) {E : Type} (label : Row h×Fin h→E)
  (ready : CountedReady v h width v.maxBits) (extent : v.wideFundedSize h width v.maxBits≤S)
  (low : 2^h≤S) (room : S+2*(2^h)<2^(Native.wordBits h (2^v.W) Native.copies)) (e : E→Bool)
  (word : Bits (CalendarTape.bits (v.wideSelector h width age budget small).format.slot (events v.mesh)))
  (π : Equiv.Perm (Row h)) (auth : ∀i,CalendarTape.WordSlots.exposed label e i=π i)
local notation "image" => (L).tape es label (v.wideFixedCPUInput h width S highSeed) e word
local notation "raw" => (L).header es word highSeed
local notation "seed" => v.wideFundedRaw h width v.maxBits raw
local notation "origin" => v.wideSignedMidAt h width S stock v.radius π.symm o (v.wideFundedRaw h width v.maxBits highSeed)
local notation "occurs" => ∃! j : CalendarTape.Path slot es origin,CalendarTape.encode slot es origin j=word
local notation "mid" => v.wideSignedMidAt h width S stock v.radius π.symm o seed
local notation "target" => v.wideInverseTarget h width age budget small S highSeed π word
local notation "invCode" => TagInverse.program W h S
local notation "checkout" => v.wideSignedCheckoutAt h width S stock v.radius π.symm o seed

set_option maxHeartbeats 1400000 in
include ready extent low room auth in
/-- This actual run applies to every private bit string, including one rejected by the
signed calendar. The output memory is its ordinary native checkout. -/
theorem wide_inverse_admission {m : ℕ} (l : WideCPU.Layout m) (scratch : l.tagScratch=S)
    (lim : v.GateRoom h width v.maxBits l S) (large : v.programRoomHeight≤h) :
    let gate:=(v.wideGates h width v.maxBits l S lim).1
    gate.Ran image checkout ∧ gate.observed image (gate.zeroFlag (F:=F) (0 : Fin 1))=(if occurs then 1 else 0) := by
  intro gate
  have bound:=(v.wide_funded_extent h width v.maxBits).trans extent
  have invert : (invCode).Exec (initialMemory S image) (initialMemory S target) (TagInverse.ticks h) :=
    v.wide_tag_inverse_entry h width age budget small S highSeed label bound low room e word π auth
  have layout:=v.catalyst_market_layout_at P h width S (v.wideGeometryPrefix h width).2.1 bound
  have mounted:=(v.wide_funded_stock_at_size h width v.radius π.symm raw v.maxBits S extent
    ready.height budget small).mounted_all
  have widthPos : 0<W:=by unfold Native.wordBits;omega
  have flags:=(historyFlag_fits_of_dated C A widthPos (fun a _=>v.catalyst_dated_verdict P h width _ _ _ _ _ _ a))
  have guard : flag+1<2^W:=by have n:=Nat.two_pow_pos h;omega
  have checker : (Boot.compactProgram C flag).Exec (initialMemory S target) checkout
      (Native.Compact.constant D*2^h+checkedCost C) :=
    Boot.compact_checked C flag V layout (Nat.two_pow_pos _) π.symm
    (v.wideSignedWords h width stock v.radius π.symm o seed)
    (v.wide_signed_words_authentic h width stock v.radius π.symm o seed) mounted flags guard
  have run : (v.widePrograms h width v.maxBits l).1.Exec (initialMemory S image) checkout
      (v.wideProgramTicks h width v.maxBits l).1 := by
    change ((TagInverse.program W h l.tagScratch).seq (Boot.compactProgram C flag)).Exec _ _ _
    rw [scratch]
    exact @Procedure.Exec.then W invCode (Boot.compactProgram C flag) _ _ _ _ _ (@invert) (@checker)
  have ran : gate.Ran image checkout :=
    Gate.ofProcedure_run (v.widePrograms h width v.maxBits l).1 (flag:Word W) 0
      (fun _ : Fin 1 => (flag:Word W)) gate.m lim.word lim.smallFirst lim.initial lim.firstClock
      image checkout (v.wideProgramTicks h width v.maxBits l).1 (Nat.lt_succ_self _) (@run)
  have fits : gate.S+(gate.f+gate.u)≤2^gate.m :=
    (le_max_right (2^h) _).trans (Nat.le_pow_clog (by decide : 1<2) _)
  have record:=(v.wideGates_word_room h width v.maxBits l S lim large).1
  refine ⟨ran,?_⟩
  rw [prefix_run gate image (0 : Fin 1) checkout ran fits record]
  change (if (checkout ((flag:Word W).val)).val=0 then (1:F) else 0)=_
  rw [Fin.val_cast_of_lt (by omega : flag<2^W)]
  have accepts:=v.wide_funded_admission h width age budget small v.maxBits S bound v.radius π.symm highSeed word
  have yes : (checkout flag).val=0 ↔ occurs :=
    (show (checkout flag).val=0 ↔ checkout flag=0 from
      ⟨fun h=>Fin.ext h,fun h=>congrArg Fin.val h⟩).trans accepts
  exact if_congr yes rfl rfl

/-- An accepted original signed tape yields the entire native paid receipt and a
direct sequential execution from the very same physical header as the admission gate. -/
abbrev wide_inverse_accepted (found : occurs) :=
  let bound:=(v.wide_funded_extent h width v.maxBits).trans extent
  let invert : (invCode).Exec (initialMemory S image) (initialMemory S target) (TagInverse.ticks h) :=
    v.wide_tag_inverse_entry h width age budget small S highSeed label bound low room e word π auth
  let admitted:=(v.wide_funded_admission h width age budget small v.maxBits S bound v.radius π.symm highSeed word).2 found
  let archive:=CountedReady.execute v h width v.maxBits ready S extent π.symm raw 0 admitted
  And.intro archive (@Procedure.Exec.then W invCode _ _ _ _ _ _ (@invert) archive.2.1)

include extent low room auth in
/-- Prepend the authentic inverse execution after the paid suffix has been closed.
This preserves the literal association of native procedure blocks in the installed gate. -/
theorem wide_paid_exec_after_inverse {m : ℕ} (l : WideCPU.Layout m) (scratch : l.tagScratch=S)
    (_lim : v.GateRoom h width v.maxBits l S) (out : Memory W)
    (done : let paid:=(v.wideWidthLayout h width (v.widePaidSlices h width v.maxBits)).bank (es).length
      (l.finish (v.wideCountedPrefix h width v.maxBits) paid).Exec
        (initialMemory S (v.wideInverseTarget h width age budget small S highSeed π word)) out
        (l.ticks (v.wideCountedTime h width v.maxBits) paid)) :
    (v.widePrograms h width v.maxBits l).2.Exec (initialMemory S image) out
      (v.wideProgramTicks h width v.maxBits l).2 := by
  have bound:=(v.wide_funded_extent h width v.maxBits).trans extent
  have invert : (invCode).Exec (initialMemory S image) (initialMemory S target) (TagInverse.ticks h) :=
    v.wide_tag_inverse_entry h width age budget small S highSeed label bound low room e word π auth
  have run : (v.widePrograms h width v.maxBits l).2.Exec (initialMemory S image) out
      (v.wideProgramTicks h width v.maxBits l).2 := by
    change ((TagInverse.program W h l.tagScratch).seq _).Exec _ _ _
    rw [scratch]
    exact @Procedure.Exec.then W invCode _ _ _ _ _ _ (@invert) (@done)
  exact @run

include extent low room auth in
/-- Prepend the authentic inverse execution after the paid suffix has been closed.
This preserves the literal association of native procedure blocks in the installed gate. -/
theorem wide_paid_gate_after_inverse {m : ℕ} (l : WideCPU.Layout m) (scratch : l.tagScratch=S)
    (lim : v.GateRoom h width v.maxBits l S) (out : Memory W)
    (done : let paid:=(v.wideWidthLayout h width (v.widePaidSlices h width v.maxBits)).bank (es).length
      (l.finish (v.wideCountedPrefix h width v.maxBits) paid).Exec
        (initialMemory S (v.wideInverseTarget h width age budget small S highSeed π word)) out
        (l.ticks (v.wideCountedTime h width v.maxBits) paid)) :
    (v.wideGates h width v.maxBits l S lim).2.Ran image out := by
  have bound:=(v.wide_funded_extent h width v.maxBits).trans extent
  have invert : (invCode).Exec (initialMemory S image) (initialMemory S target) (TagInverse.ticks h) :=
    v.wide_tag_inverse_entry h width age budget small S highSeed label bound low room e word π auth
  have run : (v.widePrograms h width v.maxBits l).2.Exec (initialMemory S image) out
      (v.wideProgramTicks h width v.maxBits l).2 := by
    change ((TagInverse.program W h l.tagScratch).seq _).Exec _ _ _
    rw [scratch]
    exact @Procedure.Exec.then W invCode _ _ _ _ _ _ (@invert) (@done)
  exact Gate.ofProcedure_run _ _ _ (Gate.denseAddr lim.upper) _ lim.word lim.smallPaid lim.initial lim.paidClock
    _ _ _ (by omega) run

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
