import OAI.Computability.VPVNP.CompressorRefreshBlockPlan
import OAI.Computability.VPVNP.CompressorHeaderOperands

/-!
# Memory operands of the installed expander-refresh workers

The worker recipes only read the six inputs from the current level. The
admission grid and supply weights in the selected motif are fixed literals.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords

open BurstRAM PhaseRecipe

namespace TermWorker

open MotifGrid MotifBlocks MotifConversion MotifSelector
open private demandLiterals gridLiterals from OAI.Computability.VPVNP.CompressorTermWorkerRecipe

variable {k : Type*} [_root_.Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

theorem motifExprs_reads {d n w : ℕ} (order : Fin d ≃ D) (supply : Fin n ≃ S)
    (head : Fin 4 → Expr) (region : ℕ → Prop) (pub : Fin 5 → BurstRAM.Word w)
    (s : BurstRAM.Word w) (m : Memory w) (ok : ∀ i, (head i).ReadsFrom region pub s m)
    (i : Fin (motifPass B order n).params) :
    (motifExprs B order supply head i).ReadsFrom region pub s m := by
  have demand (scale : ℕ) (j : Fin (d+1)) :
      (demandLiterals order p scale j).ReadsFrom region pub s m := by
    cases j using Fin.lastCases <;> simp [demandLiterals,Expr.ReadsFrom]
  unfold motifExprs
  cases i using Fin.addCases with
  | left i => simpa only [Fin.append_left] using ok i
  | right i =>
    rw [Fin.append_right]
    cases i using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      cases i using Fin.addCases <;> simp only [Fin.append_left,Fin.append_right] <;>
        first | exact demand _ _ | trivial
    | right i =>
      rw [Fin.append_right]
      cases i using Fin.addCases <;> simp only [Fin.append_left,Fin.append_right] <;>
        first | exact demand _ _ | trivial

end TermWorker

namespace PortRefresh.LevelRecipe

variable {w : ℕ} (D : ℕ → Prop) (pub : Fin 5 → BurstRAM.Word w) (state : Word w) (m : Memory w)

/-- At the given public words, state and memory, evaluating the six refresh level inputs reads
only addresses satisfying the supplied predicate. -/
structure InputReads (I : Input) : Prop where
  start : I.start.ReadsFrom D pub state m
  vertices : I.vertices.ReadsFrom D pub state m
  lanes : I.lanes.ReadsFrom D pub state m
  oldOut : I.oldOut.ReadsFrom D pub state m
  oldShift : I.oldShift.ReadsFrom D pub state m
  oldWidth : I.oldWidth.ReadsFrom D pub state m

open Compression
variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {I : Input} (h : InputReads D pub state m I)
local notation "R" => Expr.ReadsFrom D pub state m
local notation "s" => RefreshBlockPlan.shape B

include h in
theorem stage_supported (j : Stage s) :
    HeaderOperands.Supported D pub state m (RefreshBlockPlan.stage B I j) := by
  have ps : R (sites s I) := ⟨⟨h.vertices,trivial⟩,h.lanes⟩
  have bl : R (blocks I) := ⟨h.vertices,h.lanes⟩
  have sg : R (segments s I) := ⟨ps,trivial⟩
  have ca : R (capacity s I) := ⟨ps,trivial⟩
  have dm : R (demandStart s I) := ⟨h.start,trivial,sg⟩
  have tm : R (termStart s I) := ⟨dm,bl,trivial⟩
  have sp : R (supplyStart s I) := ⟨tm,bl,trivial⟩
  have tg : R (targetPort s I) := ⟨sp,ps,trivial⟩
  have rv : R (reverseSlot s I) := ⟨tg,trivial,trivial⟩
  have out : R (outputStart s I) := ⟨rv,trivial,trivial⟩
  have col (i : Fin 6) : R (column s I i) := ⟨out,trivial,ca⟩
  have sc (i : Fin 8) : R (scratch s I i) := by
    unfold scratch
    split
    · trivial
    · exact ⟨h.start,trivial,sg⟩
  have initial : R j.initial := by cases j <;> trivial
  have stop : R (j.stop I) := by
    cases j <;> first | exact sg | exact ps | exact bl | exact ⟨ps,trivial⟩
                        | exact ⟨⟨h.vertices,trivial⟩,trivial⟩ | trivial
  let bank := TermWorker.motifExprs B.refresh (RefreshBlockPlan.order B) finProdFinEquiv.symm
  have banks (k : Stage s) (z : Fin (k.arity (RefreshBlockPlan.term B).params)) :
      R (k.bank I S.degree_bounds.2 S.graph (RefreshBlockPlan.order B) bank z) := by
    cases k with
    | gather => fin_cases z; exacts [sc 0,h.lanes,h.oldWidth,sc 1]
    | bundles =>
      fin_cases z
      exacts [h.lanes,h.oldOut,sc 2,sc 3,sc 4,h.oldShift,True.intro,True.intro]
    | offsets => exact sc _
    | demand k =>
      have choose : R (if (RefreshBlockPlan.order B k).1 then scratch s I 1
          else scratch s I 7) := by
        split <;> exact sc _
      fin_cases z <;> first | exact h.lanes | exact choose | exact dm | trivial
    | term =>
      apply TermWorker.motifExprs_reads
      intro n
      fin_cases n <;> first | exact dm | exact tm | trivial
    | supply => fin_cases z <;> first | exact h.lanes | exact tm | exact sp | trivial
    | rom k => fin_cases z <;> first | exact tg | exact rv | trivial
    | slot k =>
      fin_cases z
      exacts [True.intro,True.intro,True.intro,h.lanes,True.intro,sc 2,sc 4,
        tg,rv,sp,col 3,col 4,col 5]
    | base => fin_cases z <;> first | exact h.lanes | exact col _ | trivial
  exact ⟨initial,stop,fun i ↦
    banks j (Fin.cast (j.worker_params S.degree_bounds.2 (RefreshBlockPlan.term B)) i)⟩

end PortRefresh.LevelRecipe
end CompressorRecords

end

end VPVNP
end Computability
end OAI
