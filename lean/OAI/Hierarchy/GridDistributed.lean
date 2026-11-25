import OAI.Hierarchy.GridNativeEvaluator
import OAI.ThreeFlat.RAM.CapacityPadding
import OAI.Hierarchy.GridDescription
import OAI.Hierarchy.GridThroughIdle
import OAI.Hierarchy.GridSelector
import OAI.Hierarchy.GridProgrammed
import OAI.Hierarchy.GridTickAddresses
import OAI.Hierarchy.FactorSchedule
import OAI.ThreeFlat.Diagonal.NativeTrace

namespace OAI
/-! # The genuine history and wire summands on the self-programmed grid

The accepted selector is decoded by the chronological prefix reader. The
nonidentity scalar at one tick is the product of precisely its assigned
occurrences in the load allocator. Multiplying the native tick values on
their independent pin vectors recovers the contraction of the evaluator's
weighted trace on its original paired inputs. -/

noncomputable section
namespace Hierarchy.GridThrough
open ThreeFlat
open Diagonal Diagonal.HistoryContraction
open UniversalGrid
open scoped Classical BigOperators

variable {F : Type} [Field F] {k p q n e a cap : ℕ}
variable (N : BitNetwork F p) (X : Catalyst.Approximation F k (q*p)) (dir : Fin e → Fin k)
variable (control : Bits a → Bits (cap+1) → Option (Setting X n e dir)) (code : Bits a)
variable {S : Shape} (P : Plan F S) (C : P.Codes) (bits : P.History → ℕ)
variable (order : (h : P.History) → (P.finish h).Site ≃ Fin (Fintype.card (P.finish h).Site))
variable (wire : (h : P.History) → (Fin (bits h) → Bool) ≃ (P.finish h).Boundary)
variable (seed : GridDiagonal.Pins (Fin e) → S.Factors F)

def cellFactor (z : GridSelector.Trace P bits)
    (i : Fin (Fintype.card (P.finish z.1).Site)) (x : GridDiagonal.Pins (Fin e)) : F :=
  let v := (order z.1).symm i
  P.cells z.1 (seed x) v ((P.finish z.1).graph.atVertex (wire z.1 z.2) v)

theorem sum_cellFactor (x : GridDiagonal.Pins (Fin e)) :
    (∑ z : GridSelector.Trace P bits, ∏ i, cellFactor P bits order wire seed z i x) =
      S.contract (seed x) := by
  classical
  rw [P.contract_eq_cells,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro h _
  change (∑ b : Fin (bits h) → Bool, ∏ i, cellFactor P bits order wire seed ⟨h,b⟩ i x) = _
  rw [← (wire h).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  exact (order h).symm.prod_comp (fun v => P.cells h (seed x) v ((P.finish h).graph.atVertex (wire h b) v))

/-- The real grid holes read disjoint copies of the universal tick, and use
the same list of factor occurrences as the list that was budgeted. -/
theorem eval_assigned (Q : Program (Fin e) n (q*p) X.width) (all : ∀ i,Q.touch i≠none)
    {d b : ℕ} (w : ℕ) (cost : Fin b → Fin d → ℕ) (factor : Fin b → F)
    (x : GridDiagonal.Pins (Fin e)) (hq : 0<q)
    (runs : ∀ c j, N.eval (fun i => Q.dataBits x c (finProdFinEquiv (j,i))) =
      ((FactorAllocation.factors w cost (List.ofFn id) (GridTicks.index (c,j))).map factor).prod) :
    Q.wiring.eval (Catalyst.ideal X.width (Catalyst.tickProduct N q)) x=∏ i, factor i := by
  classical
  rw [Q.eval_ticks N all]
  simp_rw [runs]
  let work (t : GridTicks.Tick k (n+1) q) := ((FactorAllocation.factors w cost (List.ofFn id) t).map factor).prod
  calc
    _ = ∏ ij : Cell k n × Fin q, work (GridTicks.index ij) := by rw [Fintype.prod_prod_type]
    _ = ∏ t, work t := GridTicks.index.prod_comp work
    _ = ((List.ofFn id).map factor).prod :=
      FactorAllocation.prod_factors_all (by positivity) w cost (List.ofFn id) factor
    _ = _ := by simp [List.map_ofFn,List.prod_ofFn]

/-- A single honest controller description and its selected native tick
computations suffice. The spectrum estimate can still quantify over every
description. The evaluator equality reaches only the original weighted
machine contraction, before any compression summation. -/
def distributed (hc : GridSelector.Room P C bits cap)
    (program : Option (GridSelector.Trace P bits) → Setting X n e dir)
    (recorded : ∀ s, control code s=(GridSelector.decode P C bits cap s).map program)
    (noTouches : ∀ i, (program none).1.touch i=none)
    (one : ∀ c, Catalyst.tickProduct N q ((program none).1.dataBits (fun _ => false) c)=1)
    (touched : ∀ z i, (program (some z)).1.touch i≠none)
    {d : ℕ} (w : ℕ) (cost : (z : GridSelector.Trace P bits) →
        Fin (Fintype.card (P.finish z.1).Site) → Fin d → ℕ)
    (hq : 0<q)
    (runs : ∀ z x c j, N.eval (fun i => (program (some z)).1.dataBits x c (finProdFinEquiv (j,i))) =
      ((FactorAllocation.factors w (cost z) (List.ofFn id) (GridTicks.index (c,j))).map
        (fun i => cellFactor P bits order wire seed z i x)).prod)
    (evaluates : ∀ x, (grid N X dir control).accelerated code x = S.contract (seed x)) :
    (grid N X dir control).Distributed code := by
  classical
  let G := grid N X dir control
  have valid (s : Bits (cap+1)) : G.Valid code s ↔ (GridSelector.decode P C bits cap s).isSome := by
    change ((control code s).map _).isSome = true ↔ _
    rw [recorded]
    cases GridSelector.decode P C bits cap s <;> rfl
  let E := (Equiv.subtypeEquivRight valid).trans (GridSelector.validEquiv P C bits cap hc)
  refine {
    Trace := GridSelector.Trace P bits
    finite := inferInstance
    factors := fun z => Fintype.card (P.finish z.1).Site
    scalar := cellFactor P bits order wire seed
    decode := E
    evaluator := fun x => (evaluates x).trans (sum_cellFactor P bits order wire seed x).symm
    at_selector := ?_
  }
  intro s x
  have hit : GridSelector.decode P C bits cap s.val = some (E s) := (Option.some_get ((valid s.val).mp s.property)).symm
  have stored : control code s.val = some (program (E s)) :=
    (recorded s.val).trans (congrArg (Option.map program) hit)
  change (((control code s.val).map (fun u => u.1.wiring)).elim 0
    (fun W => W.eval (Catalyst.ideal X.width (Catalyst.tickProduct N q)) x))=_
  rw [stored]
  cases val : E s with
  | none => exact (program none).1.eval_identity _ noTouches one x
  | some z =>
    exact eval_assigned N X (program (some z)).1 (touched z) w (cost z)
      (fun i => cellFactor P bits order wire seed z i x) x hq (runs z x)

section Native
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory RAM
open GridNativeEvaluator

variable [Fintype F] {W tp tr tk SSize depth start budget : ℕ}
variable (recv : Machine W tp tr tk) (emit : PhysicalProcedure.Procedure W)
variable (hf : Fintype.card F≤2^W)
local notation "accelerator" => GridNativeEvaluator.machine emit start (cap+1)
  (GridNativeEvaluator.parameters (e:=e) (n:=n) X hf)
variable {up ur uk : ℕ}
variable (hp : (9+emit.labels)+35≤up) (hr : emit.registers+10≤ur) (hk : emit.slots+5≤uk)
local notation "padded" => CapacityPadding.pad accelerator hp hr hk
local notation "bytes" => GridDescription.code (q:=a) recv padded
local notation "mount" => e*2+RAM.SelfAdvice.textSize W tp tk
local notation "time" => GridNativeEvaluator.tailTime (e:=e) (n:=n) X

/-- The accelerator and its native trace read the same public and same
external data. In particular the bytes that the controller reads when it
constructs tick literals include the very instruction table being traced. -/
theorem accelerated_trace
    (footprint : GridNativeEvaluator.footprint (e:=e) (n:=n) X ≤ 2^W)
    (selRoom : start+(cap+1)<2^W) (st : Word W) (extra : ℕ)
    (codeRoom : SelfAdvice.Fits W tp tk up uk 0 a)
    (fixed : ℕ→Bool)
    (fit : NativeTrace.Fits padded SSize mount depth ((extra+time+budget)+4+5*(cap+1)))
    (x : GridDiagonal.Pins (Fin e))
    (writer : ∀ s : Bits (cap+1),
      let tape := GridDescription.input (x ∘ Wiring.railPin.symm) bytes fixed
      TickStageSpec.Admission (FieldCode.ofCardLe hf) emit.block emit.publicData
        (·= GuessLoop.install start s (initialMemory SSize (fun j => TraceBitHeader.binaryWord W (tape j))))
        (fun _ => (control bytes s).isSome) (fun _ out => ∀ v, control bytes s=some v →
          ∀ i<BitLayout.footprint (GridNativeEvaluator.net X v.1), out i =
            BitLayout.memory (GridNativeEvaluator.net X v.1) (FieldCode.ofCardLe hf)
              (x ∘ Wiring.railPin.symm) (fun _ => false) i) budget) :
    (grid N X dir control).accelerated bytes x =
      (NativeTrace.network padded fit hf st).eval
        (fun i => GridDescription.input (x ∘ Wiring.railPin.symm) bytes fixed i.val) := by
  let tape := GridDescription.input (x ∘ Wiring.railPin.symm) bytes fixed
  let m := initialMemory SSize (fun j => TraceBitHeader.binaryWord W (tape j))
  let read (s : Bits (cap+1)) := (control bytes s).map Subtype.val
  have native (s : Bits (cap+1)) : TickStageSpec.Admission (FieldCode.ofCardLe hf) emit.block
      emit.publicData (·=GuessLoop.install start s m) (fun _ => (read s).isSome)
      (fun _ out => ∀ v, read s=some v → ∀ i<BitLayout.footprint (GridNativeEvaluator.net X v),
        out i=BitLayout.memory (GridNativeEvaluator.net X v) (FieldCode.ofCardLe hf)
          (x ∘ Wiring.railPin.symm) (fun _ => false) i) budget := by
    intro p' r' K' M P' R pub exit installed mounted c mem pc pre
    have issued := writer s M P' R pub exit installed mounted c mem pc pre
    cases h : control bytes s with
    | none => simpa [read,h] using issued
    | some v => simpa [read,h] using issued
  rw [GridDescription.native_trace recv padded codeRoom hf fit st,CapacityPadding.value_pad]
  rw [GridNativeEvaluator.value_eq X emit start (cap+1) budget hf footprint selRoom m st x read native extra]
  apply Finset.sum_congr rfl
  intro s _
  cases h : control bytes s <;> simp [UniversalGrid.Grid.row,grid,read,h]


end Native

end Hierarchy.GridThrough
end

end OAI
