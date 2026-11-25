import OAI.Computability.BorderVNP.FiniteProfileContinuation
import OAI.Computability.BorderVNP.FiniteEvaluatorBoundedSequence
import OAI.Computability.BorderVNP.TransmissionHeaderPreserved

/-! # The unique physical history prefix at a finite field team

The zero matrix-pin width in §3.4 leaves a single returning history for a valid
profile. Its exact register and memory pair carries the copied header, substituted
processor inputs, and emitted geometry words into the remaining field evaluator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM TeamContraction RoutingISA RoutingISA.Evaluator PackedHistoryCircuit
open FiniteEvaluator (weight weight_seq)
open private enterBody bodyReturnsEquiv prefixBounds from OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceSelected
open private weight_one selector_weight from OAI.Computability.BorderVNP.FiniteEvaluatorCellsNative
open private within_seq from OAI.Computability.BorderVNP.FiniteEvaluatorBoundedSequence
open private PinClear.read from OAI.Computability.BorderVNP.PackedHistoryPreparedInput

/-- The actual wide startup, selector and positive geometry prefix, linked in that order. -/
abbrev profileFront := dispatchTable wideStartup pinGeometry

variable {R r lit link inner n w o tapes states : ℕ} {Edge : Type} {Q Γ : Type} {K : Type*} [Field K]
variable (G : Wiring R r lit 0 link inner n Edge) (u : Fin (R+1)) (ext : Exterior R r link → Bool)
variable (ib hb sb header dst : ℕ) (pub : Arg → Word w) (bank : Bank w)
variable (lib : Fin 8 → TeamSite.Macro Q Γ tapes states) (ret : FieldProcessor.Returns Q Γ K tapes 8) (fuel : ℕ)
local notation "mac" => TeamSiteEvents.macros lib fuel
local notation "fields" => Wiring.processorFields G u (Fin.elim0 : Fin 0 → Bool) ext ib hb sb
local notation "loc" => Wiring.pinLayout G u ib hb sb
local notation "transfer" => Wiring.transferFrame G u header dst
local notation "orig" => processorMemory fields w
local notation "Front" => Returns profileFront pub mac bank orig

/-- The finite pin chooser uses no fresh word on any team, including team zero. -/
theorem finite_guessWidth : (loc).guessWidth = 0 := by simp [Pins.Layout.guessWidth,Wiring.pinLayout]

/-- The only guess available at this physical field site. -/
def noPin : Fin (loc).guessWidth → Bool := fun i => False.elim (by have hi := i.isLt; have zero := finite_guessWidth G u ib hb sb; omega)

/-- A receipt for the actual returned prefix, with its native field scalar, paid time,
common copied header, complete low-memory semantics and physically written row words. -/
structure FrontReceipt (z : Front) (count : ℕ) (extension : Fin 81 → Word w) (bits : List Bool)
    (clock fresh origin : ℕ) (words : Fin o → ℕ) : Prop where
  unique (y : Front) : y = z
  bound : Within (wideStartupBudget w count+(transfer).readTicks+2+clock) 0 0 z.val.1
  weight : weight pub lib ret fuel profileFront bank z.val.1 = 1
  headerAt : JointHeader.FlatAt z.val.2.2 dst bits
  rows (i : Fin o) : readings z.val.2.2 (origin+i.val) = words i
  source : ∃ (snap : BootSnapshot G u Fin.elim0 ext ib hb sb header dst wideStartup pub mac bank)
      (hs : List (TeamRAM.Event w)) (ready : Bank w) (saved : Memory w)
      (step : Returns pinGeometry pub mac (Function.update ready 10 (saved dst)) saved),
    Runs pub mac readBroadcast snap.registers snap.mem hs ready saved ∧
    (transfer).Stable (readings ready) ∧ (saved dst).val = 1 ∧ JointHeader.FlatAt saved dst bits ∧
    (∀ i : Fin 31, saved ((pub 0).val+i.val) = pub (Fin.ofNat 32 (i.val+1))) ∧
    (∀ i : Fin 81, saved ((pub 0).val+31+i.val) = extension i) ∧
    z.val = (dispatchPrefix transfer saved snap.events hs ++ step.val.1,step.val.2) ∧
    (∀ i < fresh, z.val.2.2 i = Pins.preparedMemory loc (Pins.extendGuess (noPin G u ib hb sb)) saved (loc).count i)

set_option maxRecDepth 3500 in
/-- For a given canonical exterior, this real processor prefix returns exactly when
its guard passes. On acceptance it has one chronology, with zero private choices. -/
theorem checked_front (count : ℕ) (extension : Fin 81 → Word w) (bits : List Bool) (ok : Prop)
    (clock fresh origin : ℕ) (words : Fin o → ℕ)
    (installed : CheckedProfileBoot G u Fin.elim0 ext ib hb sb header dst pub mac bank count extension bits ok
      clock fresh origin words) (before : dst+bits.length ≤ fresh) (clear : PinClear loc dst bits.length) :
    (Nonempty Front ↔ ok) ∧ (ok → ∃ z : Front,
      FrontReceipt G u ext ib hb sb header dst pub bank lib ret fuel z count extension bits clock fresh origin words) := by
  obtain ⟨snap,hs,ready,saved,bootTime,read,readTime,stable,mode,core,extended,flat,paths⟩ := installed
  have positive : (saved (transfer).dst).val ≠ 0 := by change (saved dst).val ≠ 0; omega
  let wrap := bodyReturnsEquiv (eval := pinGeometry) transfer snap.run (by decide) read stable positive
  have wrap_val (x : Returns pinGeometry pub mac (Function.update ready 10 (saved dst)) saved) :
      (wrap x).val = (dispatchPrefix transfer saved snap.events hs ++ x.val.1,x.val.2) := by
    change (snap.events++(hs++dispatchEvents transfer saved x.val.1),x.val.2) = _
    simp [dispatchPrefix,dispatchEvents,List.append_assoc]
  refine ⟨wrap.nonempty_congr.symm.trans paths.passes,?_⟩
  intro pass
  obtain ⟨E,effects⟩ := paths.outputs pass
  let empty := noPin G u ib hb sb
  let step := E empty
  let z := wrap step
  have guess := (effects empty).1
  have emptyList : List.ofFn empty = [] := by apply List.eq_nil_of_length_eq_zero; simpa using finite_guessWidth G u ib hb sb
  have noChoices : step.val.1.flatMap TeamRAM.Event.choices = [] := guess.trans emptyList
  have oneGuess (v : Fin (loc).guessWidth → Bool) : v=empty := by
    funext i; have hi := i.isLt; have zero := finite_guessWidth G u ib hb sb; omega
  have paid := (effects empty).2.1
  have pin := pinGeometry_within step.property paid
  have geometry : Within clock 0 0 step.val.1 := ⟨pin.cost,pin.length,fun e he => by
    rw [(List.flatMap_eq_nil_iff.mp noChoices) e he]; decide⟩
  obtain ⟨bc,ct⟩ := prefixBounds transfer snap.run (by decide) (by decide) read
  have loaded : snap.events.length+hs.length+2 ≤ wideStartupBudget w count+(transfer).readTicks+2 := by
    rw [snap.run.deterministic_cost (by decide)] at bootTime
    rw [read.deterministic_cost (by decide)] at readTime
    omega
  have full : Within (wideStartupBudget w count+(transfer).readTicks+2+clock) 0 0 z.val.1 := by
    rw [wrap_val,within_seq]
    exact ⟨⟨bc.cost.trans (by omega),bc.length,bc.choices⟩,
      ⟨geometry.cost.trans (by rw [ct]; omega),geometry.length,geometry.choices⟩⟩
  have phase : Runs pub mac (select pinGeometry) ready saved (dispatchEvents transfer saved step.val.1) step.val.2.1 step.val.2.2 :=
    (select_iff transfer pinGeometry ready saved stable).mpr ⟨_,rfl,by simp only [positive,ite_false]; exact step.property⟩
  have value : weight pub lib ret fuel profileFront bank z.val.1 = 1 := by
    change weight pub lib ret fuel (dispatchTable wideStartup pinGeometry) bank (snap.events++(hs++dispatchEvents transfer saved step.val.1)) = 1
    rw [dispatchTable,weight_seq pub lib ret fuel snap.run (read.seq phase),weight_seq pub lib ret fuel read phase,
      weight_one pub lib ret fuel snap.run (by decide) (by decide),weight_one pub lib ret fuel read (by decide) (by decide),
      one_mul,one_mul,selector_weight pub lib ret fuel transfer stable positive step.property]
    exact pinGeometry_pathProduct lib ret fuel step.property
  have low := paths.memory step empty guess
  refine ⟨z,fun y => ?_,full,value,?_,(effects empty).2.2.2,?_⟩
  · let chosen := E.trans wrap
    exact (chosen.apply_symm_apply y).symm.trans (congrArg chosen (oneGuess (chosen.symm y)))
  · apply flat.congr
    intro i
    exact (low _ (by have := i.isLt; omega)).trans (PinClear.read clear (Pins.extendGuess empty) saved i.val i.isLt)
  · exact ⟨snap,hs,ready,saved,step,read,stable,mode,flat,core,extended,wrap_val step,low⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
