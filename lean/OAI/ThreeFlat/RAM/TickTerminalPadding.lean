import OAI.ThreeFlat.RAM.TickFixedPadding
import OAI.ThreeFlat.RAM.SelectedPadHeader
import OAI.ThreeFlat.RAM.TickEvaluationRun
import OAI.ThreeFlat.RAM.TickProcedureContracts

namespace OAI
/-! # Terminal selected-root counters to the fixed weighted interpreter frame -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalPadding

open Computability.VPVNP.BurstRAM PrivateRAM HistoryFactors BitLayout Contraction PhysicalProcedure
open Diagonal.TraceCircuit
open scoped Fin.CommRing

variable {F : Type*} [Field F] [Fintype F] {p H J w : ℕ}

abbrev tables (F : Type*) [Fintype F] := Fintype.card ((Fin 3→Bool)→F)

def pad (code : FieldCode F w) (header «meta» lut J : ℕ) : Procedure w :=
  ⟨_,_,1,TickPaddedROM.fixed code «meta» lut J,fun _ => (header:Word w)⟩

def procedure (code : FieldCode F w) (control header «meta» lut p H J : ℕ) : Procedure w :=
  (SelectedPadHeader.program w control header «meta» p H (tables F)).seq (pad code header «meta» lut J)

def rows (N : BitNetwork F p) («meta» : ℕ) (m : Memory w) :=
  ∀ (i : Fin N.cells) (j : Fin 4), m («meta»+4*i.val+j.val)=metadataWord (HistoryCompiledRows.library N) i j

def budget (F : Type*) [Fintype F] (b u : ℕ) :=
  let t := tables F+2
  400+((4+8*t*(6*(8*t)+10))+(5+62*(4*(b+u))))

variable (N : BitNetwork F p) (pin : Fin p→Bool) (fit : Fits (TickWeightedBank.shape F p H J) w)
variable (control header «meta» lut : ℕ)

def recorded (m : Memory w) :=
  m (control+2)=(N.cells:Word w) ∧ m (control+3)=(N.internal:Word w) ∧ rows N «meta» m ∧
    ∀ a<cellsBase p H,m a=TickMountedPins.memory pin a

/-- Placing the four live padding operands above the immutable LUT area keeps all genuine
metadata and physical source bits intact. The cost includes its real 400-step writer. -/
theorem ready (capBits : N.internal≤H) (capRows : N.cells+(H-N.internal)≤J)
    (low : cellsBase p H≤«meta») (safe : «meta»+4*J≤lut) (endTables : lut+8*(tables F+2)≤header)
    (endHeader : header+4<2^w) (ctrl : control+3<2^w) (apart : control+4≤header ∨ header+4≤control) :
    let b := H-N.internal
    let u := J-(N.cells+b)
    let code := codec (TickWeightedBank.shape F p H J) fit
    (procedure code control header «meta» lut p H J).Spec (recorded (H:=H) N pin control «meta»)
      (fun _ out => TickWeightedBank.Ready fit (addPadding N b u) ((HistoryCompiledRows.library N).padded b u)
        pin «meta» lut out) (budget F b u) := by
  intro b u code
  let hdr (m : Memory w) := ∀ j : Fin 4, HistoryPadDriver.header (header:Word w) m j =
    ![(«meta»+4*N.cells:ℕ),(b:Word w),(hiddenBase p+N.internal:ℕ),((tables F):Word w)] j
  let lowFrame (m : Memory w) := ∀ a<cellsBase p H,m a=TickMountedPins.memory pin a
  let good (m : Memory w) := hdr m ∧ rows N «meta» m ∧ lowFrame m
  have h₁ : (SelectedPadHeader.program w control header «meta» p H (tables F)).Spec
      (recorded (H:=H) N pin control «meta») (fun _ out => good out) 400 := by
    intro P R K M pc reg pub exit installed data c m here valid
    obtain ⟨t,ht,d,out,run,atExit,headerOk,keep⟩ := SelectedPadHeader.run control header «meta» p H
      (tables F) N.cells N.internal endHeader ctrl capBits apart M pc reg pub exit installed data c m here
        ⟨valid.1,valid.2.1⟩
    refine ⟨t,ht,d,out,run,atExit,?_,?_,?_⟩
    · intro j
      refine (headerOk j).trans ?_
      fin_cases j <;> simp [b,hiddenBase];
        exact (Fin.cast_val_eq_self (b : Word w)).symm
    · intro i j
      rw [keep _ (Or.inl (by have := i.isLt; have := j.isLt; omega))]
      exact valid.2.2.1 i j
    · intro a ha
      rw [keep _ (Or.inl (by omega))]
      exact valid.2.2.2 a ha
  have h₂ : (pad code header «meta» lut J).Spec good
      (fun _ out => TickWeightedBank.Ready fit (addPadding N b u) ((HistoryCompiledRows.library N).padded b u)
        pin «meta» lut out) ((4+8*(tables F+2)*(6*(8*(tables F+2))+10))+(5+62*(4*(b+u)))) := by
    intro P R K M pc reg pub exit installed data c m here valid
    let publish : Fin 1 → Fin K := pub
    have base : M.publicData (publish 0)=(header:Word w) := data (0:Fin 1)
    have rom : (TickPaddedROM.fixed code «meta» lut J).Installed M pc reg (fun _=>publish 0) exit := by
      have eq : (fun _ : Fin 1=>publish 0)=publish := funext fun i => congrArg publish (Subsingleton.elim _ _)
      rw [eq]
      exact installed
    obtain ⟨t,ht,d,out,atExit,run,store,keep⟩ := TickPaddedROM.advance_fixed code N b u J «meta» lut
      (by dsimp [u,b]; omega) M (publish 0) pc reg exit rom c m here safe
      (by change lut+8*(tables F+2)<2^w; omega)
      (by rw [base]; exact valid.1) (by
        intro j
        right
        rw [base]
        have hj := j.isLt
        have addr : ((header:Word w)+(j.val:Word w)).val=header+j.val := by
          rw [← Nat.cast_add,Fin.val_cast_of_lt (by omega)]
        change lut+8*(tables F+2)≤((header:Word w)+(j.val:Word w)).val
        rw [addr]
        omega) valid.2.1
    exact ⟨t,ht,d,out,run,atExit,store,fun a ha => (keep a (ha.trans_le low)).trans (valid.2.2 a ha)⟩
  intro _ _ _ machine
  exact Procedure.Spec.mono (A:=procedure code control header «meta» lut p H J)
    (Procedure.Spec.seq (A:=SelectedPadHeader.program w control header «meta» p H (tables F))
      (B:=pad code header «meta» lut J) h₁ h₂ (fun _ _ h => h))
    (fun _ h => h) (fun _ _ h => h.choose_spec.2) le_rfl machine

end ThreeFlat.RAM.TickTerminalPadding

end
end OAI
