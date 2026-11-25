import OAI.Computability.NearSquareRoot.CommonAlphabetPublicNumbering
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingCore
import OAI.Computability.NearSquareRoot.ScheduleStagingDigit

/-! # Effective physical digit-call rows on the staging bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open CommonAlphabet IntegerMultiplication TM

namespace EffectiveRows
variable {A B I : Type} {Q : ℕ → Type}
variable (a : Numbering A) (b : Numbering B) (i : Numbering I)
    (q : ∀ j, Numbering (Q j)) (m : ∀ j, Rule A (Q j) I)

/-- Apply a fixed read/write track translation, preserving the current head symbol's auxiliary tracks. -/
theorem symbols (track : StagingBank.Track A B) (base : EffectiveRows a i q m) :
    EffectiveRows b i q (fun j => StagingBank.symbols track (m j)) := by
  obtain ⟨f,hf,correct⟩ := base
  let read := Routing.lookup (i.arrow b) fun h => ((i.arrow a).equiv (track.read ∘ h)).val
  let write := Routing.lookup₂ (i.arrow b) (i.arrow (a.prod Numbering.move)) fun h op =>
    ((i.arrow (b.prod Numbering.move)).equiv (fun k => (track.write (h k) (op k).1,(op k).2))).val
  let row (j : ℕ) (p : ℕ × ℕ) := (f j (p.1,read p.2)).map (fun z => (z.1,write p.2 z.2))
  have hr : Computable read := (Routing.primrec_lookup _ _).to_comp
  have hw : Computable₂ write := (Routing.primrec_lookup₂ _ _ _).to_comp
  refine ⟨row,Computable.option_map (hf.comp Computable.fst
    ((Computable.fst.comp Computable.snd).pair (hr.comp (Computable.snd.comp Computable.snd))))
    ((Computable.fst.comp Computable.snd).pair (hw.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) (Computable.snd.comp Computable.snd))),?_⟩
  intro j s h
  simp only [row,read,Routing.lookup_rank,correct,StagingBank.symbols]
  cases m j s (track.read ∘ h) with
  | none => rfl
  | some z => simp [write,Routing.lookup₂_rank]

end EffectiveRows

namespace StagedDigit
open StagingPorts

/-- Fixed finite types may be tabulated once and for all across the family. -/
noncomputable def fixed (G : Type) [Finite G] : Numbering G := by
  letI := Fintype.ofFinite G
  exact ⟨_,Fintype.equivFin G⟩

variable {X J I : Type} {Q : ℕ → Type} [DecidableEq J] [DecidableEq X] [Fintype I]
variable (q : ∀ j, Numbering (Q j))

noncomputable def states (j : ℕ) : Numbering (StagingDigit.PC (Q j) I) :=
  ((fixed StagingCopy.Phase).sum (q j)).sum (fixed (Option I → Reset.Phase))

theorem size (eff : Computable fun j => (q j).size) :
    Computable fun j => (states (I:=I) q j).size :=
  Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (Computable.const _) eff) (Computable.const _)

theorem start : Computable fun j => ((states (I:=I) q j).equiv StagingDigit.start).val :=
  Computable.const ((fixed StagingCopy.Phase).equiv .start).val

/-- The reset and copy routines have fixed tables. The indexed source table is
executed on a fixed route between them, with its actual entry rank. -/
theorem rows (a : Numbering (StagingReset.Symbol X)) (i : CommonAlphabet.Numbering I) (bank : Numbering (Bank J I))
    (one : J) (e : Encoding X) (s : X) (hs : ∀ t, s ≠ e.embed t)
    (m : ∀ j, Rule Public.Letter (Q j) (Pipeline.Index I)) (entry : ∀ j, Q j)
    (eff : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i) q m)
    (count : Computable fun j => (q j).size)
    (beginEff : Computable fun j => ((q j).equiv (entry j)).val) :
    EffectiveRows a bank (states q) (fun j => StagingDigit.rule one e s hs (m j) (entry j)) := by
  have call := (EffectiveRows.symbols _ a _ q m (markTrack e.read e.embed) eff).route (publicRoute one) bank
  have first := EffectiveRows.constant a bank (fixed StagingCopy.Phase) (StagingOffer.rule one e s hs)
  have mid := first.seq call (Computable.const _) entry beginEff
  have clear := EffectiveRows.constant a bank (fixed (Option I → Reset.Phase))
      (StagingPrivate.working_rule J I (e.embed none))
  exact mid.seq clear (Primrec.nat_add.to_comp.comp (Computable.const _) count)
    (fun _ _ => Reset.Phase.seekLeft) (Computable.const _)

end StagedDigit
end Generator

end NearSquareRoot
end Computability
end OAI
