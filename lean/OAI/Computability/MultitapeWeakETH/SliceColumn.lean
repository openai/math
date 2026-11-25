import OAI.Computability.MultitapeWeakETH.SliceLookup
import OAI.Computability.MultitapeWeakETH.TerminalProgram

/-! # Evaluating the recorded slice frames of one shrinking column -/

namespace OAI.Computability.MultitapeWeakETH.SliceLookup

open IntegerMultiplication Code VPVNP BurstRAM BurstRAM.PrivateRAM PairSimulation NativeGrid
open CompressorRecords PhaseRecipe ResidentColumn
open scoped Fin.CommRing
noncomputable section

/-- The two offset fields exchange roles for a reversed copy. -/
def frameWord (s : Setup) (offset : ℕ) : Expr := .load (s.frame.add (.lit offset))

def startExpr (s : Setup) := s.source.add (frameWord s (if s.reverse then 1 else 0))
def targetExpr (s : Setup) := s.destination.add (frameWord s (if s.reverse then 0 else 1))

variable {D : Type} [Codec D] (eval : Expr → D → Bits.Word) (ep : ∀ e, Poly (eval e))
  (read prior : D × Bits.Word → Bool)

def hit (s : Setup) (q : D × Bits.Word) :=
  locate (((eval (startExpr s) q.1,eval (targetExpr s) q.1),eval (frameWord s 2) q.1),q.2)

def overlay (s : Setup) (q : D × Bits.Word) :=
  (hit eval s q).elim (prior q) (fun p => read (q.1,p))

include ep in
theorem overlay_poly (hr : Poly read) (hp : Poly prior) (s : Setup) : Poly (overlay eval read prior s) := by
  have h : Poly (hit eval s) :=
    ((Easy.fst.poly.compose (((ep (startExpr s)).pair (ep (targetExpr s))).pair (ep (frameWord s 2)))).pair
      Easy.snd.poly).compose locate_poly
  let has := h.compose (NearSquareRoot.PhaseTable.easyOption false (fun _ => true) (Easy.const true)).poly
  let ptr := h.compose (NearSquareRoot.PhaseTable.easyOption [] id Easy.identity).poly
  convert Poly.choose has ((Easy.fst.poly.pair ptr).compose hr) hp using 1
  funext q
  unfold overlay
  cases hit eval s q <;> rfl

variable {w : ℕ} (ctx : D) (p : Fin 5 → Word w) (state : Word w) (m : Memory w)
variable (ev : ∀ e, eval e ctx = wordBits (e.eval p state m))
local notation "E" => Expr.eval p state m
def physical (f : D × Bits.Word → Bool) (a : Word w) := PrivateFields.bitValue w (f (ctx,wordBits a))
local notation "view" => physical (w:=w) ctx

include ev in
omit [Codec D] in
theorem overlay_eq (s : Setup) (r : Row) (rec : r.Recorded s p state m)
    (reads : r.reads (view read))
    (room : 0 < r.bits.length → r.destination + r.targetOffset + r.bits.length ≤ 2^w) (addr : Word w) :
    view (overlay eval read prior s) addr = r.write (view prior) addr := by
  have frame (k : ℕ) (small : k ≤ 2) : E (frameWord s k) = m (r.frame+k) := by
    change m (E s.frame + (k : Word w)).val = _
    rw [rec.frame,← Nat.cast_add,Fin.val_cast_of_lt (by have := rec.frameFit; omega)]
  have size : (E (frameWord s 2)).val = r.bits.length := by rw [frame _ le_rfl,rec.length]
  have offsets (nonempty : 0 < r.bits.length) :
      E (startExpr s) = ((r.source + r.sourceOffset : ℕ) : Word w) ∧
        (E (targetExpr s)).val = r.destination + r.targetOffset := by
    obtain ⟨left,right⟩ := rec.offsets nonempty
    have word {x : Word w} {n : ℕ} (v : x.val = n) : x = (n : Word w) := v ▸ (Fin.cast_val_eq_self x).symm
    have endFit : r.destination + r.targetOffset < 2^w := by have := room nonempty; omega
    change E s.source + E (frameWord s _) = _ ∧ (E s.destination + E (frameWord s _)).val = _
    rw [rec.source,rec.destination]
    cases dir : s.reverse <;>
      simp only [dir,Bool.false_eq_true,ite_false,ite_true] at left right ⊢ <;>
      rw [frame 0 (by decide),frame 1 (by decide)] <;>
      simp only [Nat.add_zero,word left,word right,← Nat.cast_add,Fin.val_cast_of_lt endFit,and_self]
  change PrivateFields.bitValue w ((hit eval s (ctx,wordBits addr)).elim _ _) = _
  simp only [hit,ev]
  exact locate_copy r (fun b => read (ctx,b)) (fun b => prior (ctx,b)) _ _ _ addr size offsets room reads

/-- The list is fixed by the block schedule. Its indices are compiled into a
finite composition of tape programs, with the last writer taking precedence. -/
def column {N : ℕ} (setups : Fin N → Setup) (indices : List (Fin N)) :=
  indices.foldl (fun prev i => overlay eval read prev (setups i)) prior

include ep in
theorem column_poly (hr : Poly read) (hp : Poly prior) {N : ℕ} (setups : Fin N → Setup) (indices : List (Fin N)) :
    Poly (column eval read prior setups indices) := by
  induction indices generalizing prior with
  | nil => exact hp
  | cons j js ih => exact ih _ (overlay_poly eval ep read prior hr hp (setups j))

include ev in
omit [Codec D] in
theorem column_eq {N : ℕ} (setups : Fin N → Setup) (rows : Fin N → Row) (indices : List (Fin N))
    (record : ∀ i, (rows i).Recorded (setups i) p state m)
    (reads : ∀ i, (rows i).reads (view read))
    (room : ∀ i, 0 < (rows i).bits.length → (rows i).destination + (rows i).targetOffset + (rows i).bits.length ≤ 2^w) :
    view (column eval read prior setups indices) = writes rows indices (view prior) := by
  induction indices generalizing prior with
  | nil => rfl
  | cons j js ih =>
    have step := funext (overlay_eq eval read prior ctx p state m ev (setups j) (rows j) (record j) (reads j) (room j))
    exact (ih (overlay eval read prior (setups j))).trans (congrArg (writes rows js) step)

end
end OAI.Computability.MultitapeWeakETH.SliceLookup
