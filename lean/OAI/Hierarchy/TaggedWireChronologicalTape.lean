import OAI.Hierarchy.TaggedWireCausalTape
import OAI.Hierarchy.ProtocolRAMCalendarMarketFrame

namespace OAI
/-! # The original raw selector pages are read in increasing event order -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical
variable {W q d : ℕ} {C : Chart W q d} {X : Type} {slot : Event→Slot X}
namespace WordSlots
variable (L : WordSlots slot W)

/-- Only an earlier event has to frame a later private page. -/
def ordered (C : Chart W q d) : List Event→Prop
  | []=>True
  | e::es=>(∀t∈es,∀i : Fin (L.cells t),outside C (L.base t+i.val) e) ∧ ordered C es

theorem chronologically_read (es : List Event) (m : Memory W) (ok : mounted C es m)
    (full : L.ordered C es) : actual slot C L.read es m=L.static es m := by
  induction es generalizing m with
  | nil=>rfl
  | cons e es ih=>
    have keep : L.agrees es (after C e m) m := fun t ht j=>
      after_outside C e m (L.base t+j.val) ok.1 (full.1 t ht j)
    exact congrArg (fun b : Bits (bits slot es)=>
      (Fin.addCases (L.read e m) b : Bits ((slot e).bits+bits slot es)))
      ((ih _ ok.2 full.2).trans (L.static_congr es keep))
end WordSlots

namespace CounterROM
variable (R : CounterROM C)

theorem admit_input (es : List Event) (initial loaded : Memory W) (raw : Bits (bits R.format.slot es))
    (sep : R.format.windows.disjoint es) (forward : R.format.windows.ordered C es)
    (own : ∀a,.attempt a∈es→∀i : Fin ((C.layout a).candidates*q),protected C ((R.bank a).base+i.val) (.attempt a))
    (same : R.format.windows.agrees es loaded (R.format.windows.header es raw initial))
    (start : ReadBanks.Agree (R.hidden es) initial loaded) (ok : mounted C es loaded)
    (observed : ∀a prior tail m v,es=prior++(.attempt a::tail)→ run C prior loaded=v→
      ReadBanks.Agree (R.hidden (.attempt a::tail)) m v→mounted C (.attempt a::tail) v→R.format.observed a m v)
    (step : ∀e prior tail m v,es=prior++(e::tail)→ run C prior loaded=v→
      ReadBanks.Agree (R.hidden (e::tail)) m v→mounted C (e::tail) v→∀c:(R.format.slot e).choice m,
      (R.format.slot e).word m c=R.format.windows.read e v→
      ReadBanks.Agree (R.hidden tail) ((R.format.slot e).next m c) (after C e v)) :
    admissible C es loaded ↔ ∃! j : Path R.format.slot es initial,encode R.format.slot es initial j=raw := by
  let inv:=fun xs m v=>ReadBanks.Agree (R.hidden xs) m v ∧ mounted C xs v ∧ ∃prior,es=prior++xs ∧ run C prior loaded=v
  have check : ∀e tail m v,inv (e::tail) m v→
      (accepted C e v ↔ ∃c,(R.format.slot e).word m c=R.format.windows.read e v) := by
    rintro (a|b) tail m v h
    · obtain ⟨prior,hs,hv⟩:=h.2.2
      exact R.format.native_choice a m v (observed a prior tail m v hs hv h.1 h.2.1) h.2.1.1 (own a (by simp [hs]))
    · refine ⟨fun _=>⟨(),funext fun i : Fin 0=>Fin.elim0 i⟩,fun _=>?_⟩
      trivial
  have advance : ∀e tail m v,inv (e::tail) m v→∀c,(R.format.slot e).word m c=R.format.windows.read e v→
      inv tail ((R.format.slot e).next m c) (after C e v) := by
    intro e tail m v h c word
    obtain ⟨prior,hs,hv⟩:=h.2.2
    refine ⟨step e prior tail m v hs hv h.1 h.2.1 c word,h.2.1.2,prior++[e],by simpa using hs,?_⟩
    simp [run_append,hv,run]
  have beginRun : inv es initial loaded := ⟨start,ok,[],rfl,rfl⟩
  rw [admissible_iff R.format.slot C R.format.windows.read inv check advance es initial loaded beginRun,
    R.format.windows.chronologically_read es loaded ok forward,R.format.windows.static_congr es same,
    R.format.windows.static_header es raw initial sep]

end CounterROM
end Hierarchy.WireTelescope.CalendarTape

end
end OAI
