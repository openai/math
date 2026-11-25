import OAI.Computability.BorderVNP.DiagonalNativeModes
import OAI.Computability.BorderVNP.TeamSiteTimedContraction

/-! # The two physical broadcast modes in the timed signed diagonal contraction -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator TeamScales Filter Diagonal.Layout
open scoped Classical BigOperators

variable {R r t d link inner n w : ℕ} {Edge : Type}

/-- True native value of the installed startup and evaluator, on the original
header determined by the processor input and the external wire assignment. -/
noncomputable def packetNative (G : Wiring R r t d link inner n Edge) (eval : Code) (mac : TeamOpcode.Macros w 8)
    (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (ticks burst clock : ℕ) (ext : Exterior R r link → Bool) (u : Fin (R+1)) : ℤ :=
  let a := args u
  let F := G.processorFields u pin ext a.ibase a.hbase a.starbase
  nativeValue (processorMachine (withStartup eval) (pub u) mac (reg u) F) ticks burst clock

/-- Only the positive branch tag contributes to the evaluator term. Its signed
integer counts the same native program with the same original charged cutoff. -/
noncomputable def positiveMaskedNativeValue (G : Wiring R r t d link inner n Edge) (eval : Code) (mac : TeamOpcode.Macros w 8)
    (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (ticks burst clock : ℕ) (ext : Exterior R r link → Bool) (u : Fin (R+1)) : ℤ :=
  if modeTag (w:=w) G args pin ext u=0 then 0 else packetNative G eval mac pub reg args pin ticks burst clock ext u

/-- On each true physical packet, every nonzero signed native value forces the common
broadcast guard. The proof covers both tags and uses no assumption about success. -/
theorem packetNative_guarded (physical : UniversalMachine.Program) {a e : ℕ} (eval : Code)
    (mac : TeamOpcode.Macros w 8) (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
    (fit : fitsWith physical 64 32 r w a R link n e) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (u : Fin (R+1))
    (he : eval.withoutAccept = true) :
    let P := (withStartup eval).program
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let a := args u
    let f := G.transferFrame u a.header a.dst
    let L := G.pinLayout u a.ibase a.hbase a.starbase
    a.Fitted G u (pack u) (S.publicWords u) (adviceOffsetWith physical r 32 64 w n) →
    packetUnitBudget a.advice.count w f L ≤ S.limit.val →
    packetNative G eval mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext u ≠ 0 →
      f.Agrees (readings (modeMemory (w:=w) G args pin ext u)) := by
  intro P G a f L ready time nonzero
  let p := pack u
  by_cases zero : modeTag (w:=w) G args pin ext u = 0
  · obtain ⟨stride,count,cap,identity⟩ := ready.pinRoom
    have unit := jointPacket_unit_valueWith physical P S pack link n e fit u pin ext a.header a.dst a.ibase a.hbase a.starbase
      (S.publicWords u) mac (S.registers u) a.advice eval he S.limit.val S.burst.val (n^25)
      ready.operands ready.physical ready.gather ready.extended ready.literalOffset ready.packet ready.reference zero
      stride count cap ready.apart (fun _ => identity) time
    apply mode_agrees_of_unit G args pin ext p.reference ready.physical
    by_contra failed
    exact nonzero (unit.trans (ite_eq_right failed))
  · have small : jointBudget a.advice.count w+f.readTicks+2 ≤ S.limit.val := by
      unfold packetUnitBudget at time
      omega
    have checked := jointPacket_eval_valueWith physical P S pack link n e fit u pin ext a.header a.dst a.ibase a.hbase a.starbase
      (S.publicWords u) mac (S.registers u) a.advice eval he S.limit.val S.burst.val (n^25)
      ready.operands ready.physical ready.gather ready.extended ready.literalOffset ready.packet ready.reference zero small
    by_contra failed
    exact nonzero (checked.1 failed)

/-- A nonzero positive masked coefficient actually ran the selected evaluator
after the common packet copy. Its remaining tick allowance subtracts the physical
prefix already consumed, and the copied header and reference are available in RAM. -/
theorem positiveMasked_residual (physical : UniversalMachine.Program) {a e : ℕ} (eval : Code)
    (mac : TeamOpcode.Macros w 8) (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
    (fit : fitsWith physical 64 32 r w a R link n e) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (u : Fin (R+1)) (he : eval.withoutAccept = true) :
    let P := (withStartup eval).program
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let a := args u
    let f := G.transferFrame u a.header a.dst
    let L := G.pinLayout u a.ibase a.hbase a.starbase
    let F := G.processorFields u pin ext a.ibase a.hbase a.starbase
    let scalar := positiveMaskedNativeValue G eval mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext u
    a.Fitted G u (pack u) (S.publicWords u) (adviceOffsetWith physical r 32 64 w n) →
    packetUnitBudget a.advice.count w f L ≤ S.limit.val → scalar ≠ 0 →
    modeTag (w:=w) G args pin ext u ≠ 0 ∧ f.Agrees (readings (modeMemory (w:=w) G args pin ext u)) ∧
    ∃ used b mb, used ≤ jointBudget a.advice.count w+f.readTicks+2 ∧ F.ContainsInput mb ∧
      Frame L (readings (S.publicWords u)) (readings mb) ∧
      (∀ j < a.header, readings mb (a.dst+j) = readings (modeMemory (w:=w) G args pin ext u) (f.addr f.partner j)) ∧
      scalar = boundedValue eval (S.publicWords u) mac b mb (S.limit.val-used) S.burst.val (n^25) := by
  intro P G a f L F scalar ready time nonzero
  have tag : modeTag (w:=w) G args pin ext u ≠ 0 := fun zero => nonzero (ite_eq_left zero)
  have live : scalar = packetNative G eval mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext u :=
    ite_eq_right tag
  have guard := packetNative_guarded physical eval mac S pack fit args pin ext u he ready time (live ▸ nonzero)
  have small : jointBudget a.advice.count w+f.readTicks+2 ≤ S.limit.val := by unfold packetUnitBudget at time; omega
  have replay := jointPacket_eval_valueWith physical P S pack link n e fit u pin ext a.header a.dst a.ibase a.hbase a.starbase
    (S.publicWords u) mac (S.registers u) a.advice eval he S.limit.val S.burst.val (n^25) ready.operands ready.physical
    ready.gather ready.extended ready.literalOffset ready.packet ready.reference tag small
  obtain ⟨used,b,mb,ticks,input,frame,copied,_,eq⟩ := replay.2 guard
  exact ⟨tag,guard,used,b,mb,ticks,input,frame,copied,live.trans eq⟩

/-- The native sum has one reference column and an independent positive-evaluator
contribution. All physical zero-tag and positive-tag products come from actual
finite RAM executions on real installed wires, and mixed successful tags are impossible. -/
theorem eventually_packet_modes {ξ η : ℝ} (hξ : 0 < ξ) (small : ξ ≤ 1) (eta : η ≤ 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ (physical : UniversalMachine.Program) (R r w a d e : ℕ) (eval : Code)
      (mac : TeamOpcode.Macros w 8) (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
      (fit : fitsWith physical 64 32 r w a R (TeamScales.link ξ (R+1) n) n e)
      (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool), eval.withoutAccept = true →
      R+1 ≤ width n η → ticks ξ r n ≤ S.limit.val →
      let G := wiringWith physical (withStartup eval).program (S.withPacket pack) d (TeamScales.link ξ (R+1) n) n e fit
      (∀ u, (args u).Fitted G u (pack u) (S.publicWords u) (adviceOffsetWith physical r 32 64 w n)) →
      (∑ ext, ∏ u, packetNative G eval mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext u) =
        (if pin = (pack 0).reference then 1 else 0) +
        ∑ ext, ∏ u, positiveMaskedNativeValue G eval mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext u := by
  filter_upwards [eventually_wired_unit_columnWith hξ small eta,eventually_packetUnitBudget_le_ticks hξ small eta] with n unit budget
  intro physical R r w a d e eval mac S pack fit args pin he bound cutoff G fitted
  let V := packetNative G eval mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25)
  have agreed (ext : Exterior R r (TeamScales.link ξ (R+1) n) → Bool) (u : Fin (R+1)) (hz : V ext u ≠ 0) :
      (G.transferFrame u (args u).header (args u).dst).Agrees (readings (modeMemory (w:=w) G args pin ext u)) := by
    let a := args u
    let f := G.transferFrame u a.header a.dst
    let L := G.pinLayout u a.ibase a.hbase a.starbase
    have team : (f.teams:ℝ) ≤ (n:ℝ)^η :=
      (Nat.cast_le.mpr bound).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have h := fitted u
    have time := budget w d ((S.publicWords u) 0).val (pack u) a.advice f L h.physical rfl team h.packet h.gather.count rfl
    exact packetNative_guarded physical eval mac S pack fit args pin ext u he h (time.trans cutoff) hz
  have split := sum_mode_products G pin args (fun u => ((S.publicWords u) 0).val) (fun u => (fitted u).physical) V agreed
  apply split.trans
  apply congrArg₂ (· + ·)
  · exact unit physical R r w a d e eval mac S pack fit args pin he bound cutoff fitted
  · rfl

/-- Apply the mode decomposition to the sewn signed contraction of the genuine
trusted-clock packet program. The unit-tag part is the Kronecker reference column;
the positive part retains exactly the original finite RAM path clocks and weights. -/
theorem eventually_sewn_packet_modes {Q Γ : Type} [Fintype Q] {m g : ℕ} {ξ η : ℝ}
    (hξ : 0 < ξ) (small : ξ ≤ 1) (eta : η ≤ 1-ξ) (eval : Code) (he : eval.withoutAccept = true)
    (lib : Fin 8 → TeamSite.Macro Q Γ m g) (mark : Fin 8 → Γ) (distinct : ∀ j, (lib j).alphabet.blank ≠ mark j) :
    let P := (withStartup eval).program
    let physical := TeamSite.TimedProcessor.machine P lib mark
    ∀ᶠ t : ℕ in atTop, ∀ (R r w a d e : ℕ) (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
      (fit : fitsWith physical 64 32 r w a R (TeamScales.link ξ (R+1) (t+1)) (t+1) e) (_hr : 0 < r)
      (_geo : TeamSiteConsistency.Geometry r (t+1) ((withStartup eval).slots+1) w S.block.val S.burst.val S.limit.val e),
      w+1 ≤ t+1 → 2+e+Nat.clog 2 r ≤ t+1 →
      TeamTapeInputRoute.comparisonSize (Nat.clog 2 r) e (w+1) ≤ t+1 → S.block.val ≤ t+1 →
      R+1 ≤ width (t+1) η → ticks ξ r (t+1) ≤ S.limit.val →
      ∀ (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool),
        let G := wiringWith physical P (S.withPacket pack) d (TeamScales.link ξ (R+1) (t+1)) (t+1) e fit
        (∀ u, (args u).Fitted G u (pack u) (S.publicWords u) (adviceOffsetWith physical r 32 64 w (t+1))) →
        (∀ ext u j, ((G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase).row j).length ≤ 3*S.block.val) →
        Diagonal.signedContraction G.slot pin =
          (if pin=(pack 0).reference then 1 else 0) +
          ∑ ext, ∏ u, positiveMaskedNativeValue G eval (TeamSiteEvents.macros lib ((t+1)^25+1))
            S.publicWords S.registers args pin S.limit.val S.burst.val ((t+1)^25) ext u := by
  intro P physical
  filter_upwards [TeamSite.TimedProcessor.eventually_sewn_contraction P lib mark distinct,
    (tendsto_add_atTop_nat 1).eventually (eventually_packet_modes hξ small eta)] with t sewn modes
  intro R r w a d e S pack fit hr geo hw hd hL hblock hteams hlimit args pin G fitted own
  let mac : TeamOpcode.Macros w 8 := TeamSiteEvents.macros lib ((t+1)^25+1)
  have machineValue := sewn R r w a d (TeamScales.link ξ (R+1) (t+1)) e (S.withPacket pack) fit hr geo hw hd hL hblock pin
    (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) own
  have split := modes physical R r w a d e eval mac S pack fit args pin he hteams hlimit fitted
  exact machineValue.trans split

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
