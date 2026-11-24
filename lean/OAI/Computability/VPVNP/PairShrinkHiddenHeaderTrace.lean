import OAI.Computability.VPVNP.PairShrinkHiddenInputs
import OAI.Computability.VPVNP.CompressorRegisterSetupTrace
import OAI.Computability.VPVNP.PairShrinkRoleStages

/-!
# Canonical trace of the hidden-field header

The five external probes in the hidden-field header read offsets of the same
old-level pointer. The compiled address calculation overwrites its temporaries
before each probe. Its trace is therefore independent of the previous register
contents, including the registers used for the owner and private slot geometry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess.Header

open BurstRAM BurstRAM.PrivateRAM CompressorRecords PrimedStackRAM PhaseRecipe RowRecipe
open scoped Fin.CommRing
open private compile_value from OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
open private log_append from OAI.Computability.VPVNP.CompressorFormulaFootprint
open private room scratch_val from OAI.Computability.VPVNP.CompressorRecordRegisterSetup

variable {w r : ℕ}

/-- Each non-read assignment takes one local step, for every initial register file. -/
private theorem allTicks (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (ls : List (Assign r 5)) (rs : Regs w r) (zero : (ls.map fun l => l.rhs.reads).sum = 0) :
    (evaluate pub s m ls rs).1 = List.replicate ls.length .tick := by
  induction ls generalizing rs with
  | nil => rfl
  | cons a ls ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff] at zero
    have event : a.rhs.event m rs = .tick := by
      cases ha : a.rhs with
      | read i => simp [ha, RHS.reads] at zero
      | _ => rfl
    simp only [evaluate, event, ih _ zero.2, List.length_cons, List.replicate_succ]

private theorem compile_noReads (pub pub' : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (slot : ℕ → Fin r) (rs rs' : Regs w r) (e : Expr) (quiet : e.loads = 0) :
    (evaluate pub s m (e.compile slot 0) rs).1 = (evaluate pub' s m (e.compile slot 0) rs').1 :=
  let zero := (Expr.compile_reads e slot 0).trans quiet
  (allTicks pub s m _ rs zero).trans (allTicks pub' s m _ rs' zero).symm

private theorem compile_header (pub pub' : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (slot : ℕ → Fin r) (rs rs' : Regs w r) (i cap : ℕ)
    (fit : (Expr.header i).slots ≤ cap)
    (inj : ∀ x < cap, ∀ y < cap, slot x = slot y → x = y) :
    (evaluate pub s m ((Expr.header i).compile slot 0) rs).1 =
      (evaluate pub' s m ((Expr.header i).compile slot 0) rs').1 := by
  let e := Expr.headerAddress i
  have hf : 0 + e.slots ≤ cap := by rw [Nat.zero_add]; exact fit
  have addr (b : Fin 5 → Word w) (v : Regs w r) :
      (evaluate b s m (e.compile slot 0) v).2 (slot 0) = s + (i : Word w) :=
    compile_value b s m e slot cap 0 v hf inj
  simp only [Expr.header, Expr.compile, log_append, evaluate, RHS.event]
  rw [compile_noReads pub pub' s m slot rs rs' (Expr.headerAddress i) rfl, addr, addr]

private theorem emit_congr (n t : ℕ) (pub pub' : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (i : Fin 10) (rs rs' : Regs w (RegisterSetup.regCount (recipe n t))) :
    (evaluate pub s m (RegisterSetup.emit (recipe n t) i) rs).1 =
      (evaluate pub' s m (RegisterSetup.emit (recipe n t) i) rs').1 := by
  let f := recipe n t
  let slot := RegisterSetup.scratch f
  have inj : ∀ x < RegisterSetup.scratchCount f, ∀ y < RegisterSetup.scratchCount f,
      slot x = slot y → x = y := by
    intro x hx y hy h
    have h' := congrArg Fin.val h
    rw [show (slot x).val = _ from scratch_val f hx,
      show (slot y).val = _ from scratch_val f hy] at h'
    omega
  simp only [RegisterSetup.emit, log_append, evaluate, RHS.event]
  congr 1
  have fit := room f i
  have kinds : (f i).loads = 0 ∨ ∃ j, f i = Expr.header j := by
    fin_cases i <;> simp [f, recipe, Expr.loads, Expr.header]
  rcases kinds with quiet | ⟨j, he⟩
  · exact compile_noReads pub pub' s m slot rs rs' _ quiet
  · change (evaluate pub s m ((f i).compile slot 0) rs).1 =
      (evaluate pub' s m ((f i).compile slot 0) rs').1
    rw [he] at fit ⊢
    exact compile_header pub pub' s m slot rs rs' j _ fit inj

/-- Fixing the old level pointer determines the complete chronological log.
The word size and the selected stage constants may vary. -/
theorem headerTrace_congr (selectors stride : ℕ) (pub pub' : Fin 5 → Word w) (s : Word w)
    (m : Memory w) (rs rs' : Regs w (RegisterSetup.regCount (recipe selectors stride))) :
    (evaluate pub s m (RegisterSetup.lines (recipe selectors stride)) rs).1 =
      (evaluate pub' s m (RegisterSetup.lines (recipe selectors stride)) rs').1 := by
  let f := recipe selectors stride
  suffices h : ∀ (is : List (Fin 10)) (a b : Regs w (RegisterSetup.regCount f)),
      (evaluate pub s m (is.flatMap (RegisterSetup.emit f)) a).1 =
        (evaluate pub' s m (is.flatMap (RegisterSetup.emit f)) b).1 from h _ rs rs'
  intro is
  induction is with
  | nil => intros; rfl
  | cons i is ih =>
    intro a b
    simp only [List.flatMap_cons, log_append]
    exact congrArg₂ List.append (emit_congr selectors stride pub pub' s m i a b) (ih _ _)

/-- Canonical header trace from its external pointer and memory. -/
def canonicalTrace (selectors stride : ℕ) (s : Word w) (m : Memory w) : List (Event w) :=
  (evaluate (fun _ => 0) s m (RegisterSetup.lines (recipe selectors stride)) (fun _ => 0)).1

theorem trace_canonical {p : ℕ} (selectors stride : ℕ) (inputs : Fin 6 → Fin r)
    (vm : Fin (RegisterSetup.regCount (recipe selectors stride)) ↪ Fin r)
    (c : Config w p r) (m : Memory w) (s : Word w) (level : c.reg (inputs 5) = s) :
    trace selectors stride inputs vm c m = canonicalTrace selectors stride s m := by
  unfold trace canonicalTrace
  rw [show c.reg (inputs (Fin.last 5)) = s from level]
  exact headerTrace_congr selectors stride _ _ _ _ _ _

end PairSimulation.ShrinkHiddenGuess.Header

end VPVNP
end Computability
end OAI
