import OAI.Computability.VPVNP.CompressorRecordRegisterSetup

/-!
# The event log of register setup

Every external address used by the expression compiler is computed from
the public operands, the state word and the current memory. The scratch
registers can therefore start with arbitrary words. Even nested loads and
repeated loads of the same address have the same complete event log.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RegisterSetup

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe RowRecipe
open PrimedStackRAM (Regs)
open scoped Fin.CommRing
open private run compile_value from OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
open private scratch_val room from OAI.Computability.VPVNP.CompressorRecordRegisterSetup

variable {w r n : ℕ} (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)

private theorem events_append (xs ys : List (Assign r 5)) (rs : Regs w r) :
    (evaluate pub state m (xs ++ ys) rs).1 = (evaluate pub state m xs rs).1 ++
      (evaluate pub state m ys (run pub state m xs rs)).1 := by
  induction xs generalizing rs with
  | nil => rfl
  | cons a xs ih => exact congrArg (List.cons (a.rhs.event m rs)) (ih _)

private theorem no_read_events (xs : List (Assign r 5)) (rs ts : Regs w r)
    (noReads : (xs.map fun a => a.rhs.reads).sum = 0) :
    (evaluate pub state m xs rs).1 = (evaluate pub state m xs ts).1 := by
  induction xs generalizing rs ts with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff] at noReads
    have step : a.rhs.event m rs = a.rhs.event m ts := by
      have h := noReads.1
      cases he : a.rhs <;> first | rfl | simp [he, RHS.reads] at h
    exact congrArg₂ List.cons step (ih _ _ noReads.2)

private theorem compile_events (e : Expr) (slot : ℕ → Fin r) (cap start : ℕ) (rs ts : Regs w r)
    (fits : start + e.slots ≤ cap) (inj : ∀ i < cap, ∀ j < cap, slot i = slot j → i = j) :
    (evaluate pub state m (e.compile slot start) rs).1 =
      (evaluate pub state m (e.compile slot start) ts).1 := by
  induction e generalizing start rs ts with
  | lit n =>
    apply no_read_events
    exact Expr.compile_reads (.lit n) slot start
  | publicWord _ | state => rfl
  | load a ih =>
    have hv (s : Regs w r) := compile_value pub state m a slot cap start s fits inj
    simp only [Expr.compile, events_append]
    change _ ++ [Event.read (run pub state m (a.compile slot start) rs (slot start)) _] =
      _ ++ [Event.read (run pub state m (a.compile slot start) ts (slot start)) _]
    rw [ih start rs ts fits, hv rs, hv ts]
  | binary op a b ha hb =>
    change start + max a.slots (1 + b.slots) ≤ cap at fits
    have hL := ha start rs ts (by omega)
    have hR := hb (start+1) (run pub state m (a.compile slot start) rs)
      (run pub state m (a.compile slot start) ts) (by omega)
    simp only [Expr.compile, events_append]
    change _ ++ _ ++ [(Event.tick : Event w)] = _ ++ _ ++ [(Event.tick : Event w)]
    rw [hL,hR]

variable (f : Fin n → Expr)

private theorem emit_events (i : Fin n) (rs ts : Regs w (regCount f)) :
    (evaluate pub state m (emit f i) rs).1 = (evaluate pub state m (emit f i) ts).1 := by
  have hf : 0 + (f i).slots ≤ scratchCount f := by simpa only [Nat.zero_add] using room f i
  have inj (u : ℕ) (hu : u < scratchCount f) (v : ℕ) (hv : v < scratchCount f)
      (eq : scratch f u = scratch f v) : u = v := by
    have nums := congrArg Fin.val eq
    rw [scratch_val f hu, scratch_val f hv] at nums
    omega
  simp only [emit, events_append]
  change _ ++ [(Event.tick : Event w)] = _ ++ [(Event.tick : Event w)]
  rw [compile_events pub state m (f i) (scratch f) (scratchCount f) 0 rs ts hf inj]

/-- Evaluating all setup lines produces the same events as a zeroed
compiler bank, including the address and return value of every read. -/
theorem events_eq (f : Fin n → Expr) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)
    (rs : Regs w (regCount f)) :
    (evaluate pub state m (lines f) rs).1 = (evaluate pub state m (lines f) (fun _ ↦ 0)).1 := by
  have go (is : List (Fin n)) (xs ys : Regs w (regCount f)) :
      (evaluate pub state m (is.flatMap (emit f)) xs).1 = (evaluate pub state m (is.flatMap (emit f)) ys).1 := by
    induction is generalizing xs ys with
    | nil => rfl
    | cons i is ih =>
      simp only [List.flatMap_cons, events_append]
      rw [emit_events pub state m f i xs ys, ih]
  exact go (List.finRange n) rs (fun _ ↦ 0)

end CompressorRecords.RegisterSetup

end VPVNP
end Computability
end OAI
