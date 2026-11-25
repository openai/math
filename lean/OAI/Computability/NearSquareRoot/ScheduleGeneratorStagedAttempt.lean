import OAI.Computability.NearSquareRoot.ScheduleGeneratorStaged
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingReject
import OAI.Computability.NearSquareRoot.ScheduleStagingReject
import OAI.Computability.NearSquareRoot.ScheduleGeneratorTemplateMachine

/-! # Effective rows and emitted ROMs for complete split attempts -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator

open CommonAlphabet IntegerMultiplication TM
variable {A I : Type} {Q : ℕ → Type}

theorem EffectiveRows.reindex {a : Numbering A} {i : CommonAlphabet.Numbering I}
    {q : ∀ j, Numbering (Q j)} {m : ∀ j, Rule A (Q j) I}
    (h : EffectiveRows a i q m) (j : ℕ → ℕ) (hj : Computable j) :
    EffectiveRows (Q:=fun l => Q (j l)) a i (fun l => q (j l)) (fun l => m (j l)) := by
  obtain ⟨r,hr,rc⟩ := h
  exact ⟨fun l => r (j l),hr.comp (hj.comp Computable.fst) Computable.snd, fun l => rc (j l)⟩

namespace Staged
open ChunkControl
noncomputable section

variable [Fintype I] [DecidableEq I] (d : Driver)
variable (i : CommonAlphabet.Numbering I) (q : ∀ j, Numbering (Q j))
    (g : ∀ j, Rule Public.Letter (Q j) (Pipeline.Index I)) (e : ∀ j, Q j)

/-- A rejected guard sticks forever, so only completed products are observable halts. -/
theorem successful_rows (hq : Computable fun j => (q j).size)
    (he : Computable fun j => ((q j).equiv (e j)).val)
    (hg : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i) q g) :
    EffectiveRows (num (StagingProtection.Cell d)) (num (StagingOuter.Axis d I)).option.option
      (states d q) (fun j => StagingReject.successful d (g j) (e j)) := by
  have inner : Computable fun j => (((num (StagingControl.State d)).sum
    (StagedDigit.states (I:=I) q j)).option).size := Primrec.succ.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Computable.const _) (StagedDigit.size q hq))
  exact (rows d i q g e hq he hg).reject_boolFirst inner

abbrev axes (d : Driver) (I : Type) := Pipeline.Index (StagingProtection.Tapes d I)
abbrev tapeNum (d : Driver) (I : Type) [Fintype I] : CommonAlphabet.Numbering (axes d I) :=
  Numbering.publicIndex (num (StagingOuter.Axis d I)).option.option

variable {S : ℕ → Type} (s : ∀ k, Numbering (S k))
  (prepare : ∀ k, Rule (StagingProtection.Cell d) (S k) (axes d I)) (beginPrep : ∀ k, S k)
  (left right : ℕ → ℕ)

/-- Startup loads a fixed split on registers and marks the stage. Every subsequent transition
uses the same protected candidate machine, on the old axes of the augmented public bank. -/
def attempt (l : ℕ) :=
  TapeSequence.rule (prepare (right l))
    ((Pipeline.coreRoute _).rule (StagingReject.successful d (g (left l)) (e (left l))))
    (entry (I:=I) d (Q (left l)))

abbrev attemptNum (l : ℕ) :=
  (s (right l)).sum (states (I:=I) d q (left l))

abbrev attemptEntry (l : ℕ) : S (right l) ⊕ StagingProtection.State d (StagingDigit.PC (Q (left l)) I) :=
  Sum.inl (beginPrep (right l))

/-- Unary-indexed literal program generation, including the indexed startup and the
guarded multiplication body. The pair projections can be any computable enumeration. -/
theorem emit_attempt {M : ℕ} (enum : Universal.Tag (StagingProtection.Cell d) (axes d I) ≃ Fin (M+1))
    (hl : Computable left) (hr : Computable right)
    (hq : Computable fun j => (q j).size) (he : Computable fun j => ((q j).equiv (e j)).val)
    (hg : EffectiveRows Numbering.publicLetter (Numbering.publicIndex i) q g)
    (hs : Computable fun k => (s k).size) (hb : Computable fun k => ((s k).equiv (beginPrep k)).val)
    (hp : EffectiveRows (num (StagingProtection.Cell d)) (tapeNum d I) s prepare) :
    let a := num (StagingProtection.Cell d)
    let t := tapeNum d I
    let reads := (t.arrow a).all
    let rom := fun l => Universal.Reindex.encode ((attemptNum (I:=I) d q s left right l).equiv)
      (attemptEntry (I:=I) (Q:=Q) d beginPrep left right l) (attempt d g e prepare left right l) reads
    Computable (fun l => GeneratorPipeline.symbolWord enum (rom l)) ∧
      ∃ c : Turing.ToPartrec.Code, ∀ l, GeneratorPipeline.symbolWord enum (rom l) ∈ c.eval (unaryInput l) := by
  dsimp only
  let sn := fun l => attemptNum (I:=I) d q s left right l
  let begin := fun l => attemptEntry (I:=I) (Q:=Q) d beginPrep left right l
  have bodyRows := ((successful_rows d i q g e hq he hg).route (Pipeline.coreRoute _) (tapeNum d I)).reindex left hl
  have allRows := (hp.reindex right hr).seq bodyRows (hs.comp hr)
    (fun l => entry (I:=I) d (Q (left l))) ((start d q).comp hl)
  obtain ⟨r,eff,rc⟩ := allRows
  have height : Computable fun l => (sn l).size :=
    Primrec.nat_add.to_comp.comp (hs.comp hr) ((size d q hq).comp hl)
  have address : Computable fun l => ((sn l).equiv (begin l)).val := hb.comp hr
  have emit := computable_numbered_program (num (StagingProtection.Cell d)) (tapeNum d I) sn begin
    (attempt d g e prepare left right) ((tapeNum d I).arrow (num (StagingProtection.Cell d))).all enum r height address eff rc
  obtain ⟨c,hc⟩ := exists_unary_list_code _ emit
  exact ⟨emit,c,fun l => by rw [hc]; exact Part.mem_some _⟩

end
end Staged
end Generator

end NearSquareRoot
end Computability
end OAI
