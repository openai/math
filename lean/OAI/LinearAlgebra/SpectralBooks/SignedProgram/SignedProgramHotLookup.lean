import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramActionBits
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramHot

/-! # Reading instruction fields for one transition

The typed cells are the same coordinates checked by the program parser. A raw
reader may be lifted along a wire projection when the simulation has a larger
input register.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram.Hot
open SignedMachine ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork

variable {n a : ℕ}

/-- Each read tests whether the natural value of one table cell equals its argument. -/
abbrev CellReader (n a : ℕ) := Cell n → ℕ → BooleanNetwork a 1

def CellReader.Agrees (read : CellReader n a) (x : Fin a → Bool) (t : Table n) : Prop :=
  ∀ c v, (read c v).eval x 0 = decide (c.value t = v)

def CellReader.Bounded (read : CellReader n a) (C : ℕ) : Prop :=
  ∀ c v, (read c v).net.count ≤ C

theorem fieldBit_agrees (x : Basis n) (g : Basis (decodeGuessWidth n)) (h : WellCoded g) :
    CellReader.Agrees (fieldBit n) (Fin.append x g) (tableOfBits g) :=
  fun c v => fieldBit_correct c v x g h

theorem fieldBit_bounded (n : ℕ) : CellReader.Bounded (fieldBit n) 1 :=
  fieldBit_count n

/-- Read the checked table from selected input wires of a larger circuit. -/
noncomputable def packedReader (n : ℕ) (ρ : Fin (n + decodeGuessWidth n) → Fin a) : CellReader n a :=
  fun c v => (select ρ).comp (fieldBit n c v)

theorem packedReader_agrees (ρ : Fin (n + decodeGuessWidth n) → Fin a) (input : Basis a)
    (x : Basis n) (g : Basis (decodeGuessWidth n)) (hg : WellCoded g)
    (hρ : input ∘ ρ = Fin.append x g) :
    (packedReader n ρ).Agrees input (tableOfBits g) := by
  intro c v
  simpa only [packedReader, eval_comp, eval_select, hρ] using
    (show (fieldBit n c v).eval (Fin.append x g) 0 = _ from fieldBit_correct c v x g hg)

theorem packedReader_bounded (ρ : Fin (n + decodeGuessWidth n) → Fin a) :
    (packedReader n ρ).Bounded 1 := by
  intro c v
  simpa only [packedReader, count_comp, count_select, Nat.zero_add] using fieldBit_count n c v

/-- Read a row or tape only if its index is less than the stored count. -/
def activeBit (read : CellReader n a) (count : Cell n) (i : Fin n) : BooleanNetwork a 1 :=
  any (((List.ofFn (id : Fin (n+1) → Fin (n+1))).filter (fun k => decide (i.val < k.val))).map
    (fun k => read count k.val))

theorem activeBit_eval {read : CellReader n a} {x : Fin a → Bool} {t : Table n}
    (hread : read.Agrees x t) (count : Cell n) (hk : count.value t ≤ n) (i : Fin n) :
    (activeBit read count i).eval x 0 = decide (i.val < count.value t) := by
  apply Bool.eq_iff_iff.mpr
  rw [activeBit, any_eval, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, he⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    rw [hread] at he
    exact (of_decide_eq_true he) ▸ (of_decide_eq_true (List.mem_filter.mp hk).2)
  · intro hi
    let k : Fin (n+1) := ⟨count.value t, by omega⟩
    exact ⟨_, List.mem_map.mpr ⟨k, List.mem_filter.mpr
      ⟨List.mem_ofFn.mpr ⟨k,rfl⟩, decide_eq_true hi⟩, rfl⟩, by rw [hread]; exact decide_eq_true rfl⟩

theorem activeBit_count {read : CellReader n a} {C : ℕ} (hread : read.Bounded C)
    (count : Cell n) (i : Fin n) : (activeBit read count i).net.count ≤ (n+1)*(C+4)+1 := by
  unfold activeBit
  refine (any_count _ (c := C) (fun p hp => ?_)).trans ?_
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    exact hread _ _
  · simp only [List.length_map]
    have h := List.length_filter_le (fun k : Fin (n+1) => decide (i.val < k.val)) (List.ofFn id)
    rw [List.length_ofFn] at h
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _

def actionSignals (read : CellReader n a) : ActionSignals n a where
  kind i d := read (.row i .kind) d.val
  out i o := read (.row i .out) (outputCode o)
  state i b q := read (.row i (.move b .state)) q.val
  inputMove i b d := read (.row i (.move b .inputMove)) (directionCode d)
  workWrite i b j s := read (.row i (.move b (.write j))) (symbolCode s)
  workMove i b j d := read (.row i (.move b (.direction j))) (directionCode d)

private theorem symbolCode_inj : Function.Injective symbolCode := by
  intro s t h; cases s <;> cases t <;> simp_all [symbolCode]
private theorem directionCode_inj : Function.Injective directionCode := by
  intro s t h; cases s <;> cases t <;> simp_all [directionCode]
private theorem outputCode_inj : Function.Injective outputCode := by
  intro s t h; cases s <;> cases t <;> simp_all [outputCode]

theorem actionSignals_agrees {read : CellReader n a} {x : Fin a → Bool} {t : Table n}
    (h : read.Agrees x t) : (actionSignals read).Agrees x t := by
  unfold CellReader.Agrees at h
  constructor <;> intros <;> simp only [actionSignals, h, Cell.value, RowCell.value, MoveCell.value,
    Fin.val_inj, outputCode_inj.eq_iff, directionCode_inj.eq_iff, symbolCode_inj.eq_iff]

theorem actionSignals_bounded {read : CellReader n a} {C : ℕ} (h : read.Bounded C) :
    (actionSignals read).Bounded C := by
  constructor <;> intros <;> apply h

/-- Join table-cell reads with the current frame's state and head-symbol reads. -/
def keyInputs (read : CellReader n a) (state : Fin (n+1) → BooleanNetwork a 1)
    (inputHead : Symbol → BooleanNetwork a 1) (workHead : Fin n → Symbol → BooleanNetwork a 1) :
    KeyInputs n a where
  rowActive := activeBit read .rows
  tapeActive := activeBit read .tapes
  rowState i q := read (.row i .state) q.val
  configState := state
  rowInput i s := read (.row i .input) (symbolCode s)
  inputHead := inputHead
  rowRead i j s := read (.row i (.read j)) (symbolCode s)
  workHead := workHead

theorem keyInputs_agrees {read : CellReader n a} {x : Fin a → Bool} {t : Table n}
    (h : read.Agrees x t) {q : Fin (n+1)} {s : Symbol} {w : Fin n → Symbol}
    (state : Fin (n+1) → BooleanNetwork a 1) (inputHead : Symbol → BooleanNetwork a 1)
    (workHead : Fin n → Symbol → BooleanNetwork a 1)
    (hq : ∀ p, (state p).eval x 0 = decide (q = p))
    (hs : ∀ c, (inputHead c).eval x 0 = decide (s = c))
    (hw : ∀ j c, (workHead j c).eval x 0 = decide (w j = c)) :
    (keyInputs read state inputHead workHead).Agrees x t q s w := by
  refine ⟨activeBit_eval h .rows (Nat.le_of_lt_succ t.rows.isLt),
    activeBit_eval h .tapes (Nat.le_of_lt_succ t.tapes.isLt), ?_, hq, ?_, hs, ?_, hw⟩
  all_goals unfold CellReader.Agrees at h; intros; simp only [keyInputs, h, Cell.value, RowCell.value, Fin.val_inj, symbolCode_inj.eq_iff]

theorem keyInputs_bounded {read : CellReader n a} {C : ℕ} (h : read.Bounded C)
    (state : Fin (n+1) → BooleanNetwork a 1) (inputHead : Symbol → BooleanNetwork a 1)
    (workHead : Fin n → Symbol → BooleanNetwork a 1)
    (hq : ∀ p, (state p).net.count ≤ C) (hs : ∀ c, (inputHead c).net.count ≤ C)
    (hw : ∀ j c, (workHead j c).net.count ≤ C) :
    (keyInputs read state inputHead workHead).Bounded ((n+1)*(C+4)+1) := by
  have hc : C ≤ (n+1)*(C+4)+1 := by nlinarith
  exact ⟨activeBit_count h .rows, activeBit_count h .tapes, fun _ _ => (h _ _).trans hc,
    fun p => (hq p).trans hc, fun _ _ => (h _ _).trans hc, fun c => (hs c).trans hc,
    fun _ _ _ => (h _ _).trans hc, fun j c => (hw j c).trans hc⟩

/-- A one-bit field of the first enabled row, compiled from the packed table
and the current frame's state and head selectors. -/
noncomputable def packedLookupBit (ρ : Fin (n + decodeGuessWidth n) → Fin a)
    (state : Fin (n+1) → BooleanNetwork a 1) (inputHead : Symbol → BooleanNetwork a 1)
    (workHead : Fin n → Symbol → BooleanNetwork a 1) (field : Fin n → BooleanNetwork a 1)
    (fallback : Bool) : BooleanNetwork a 1 :=
  lookupBitNet (keySignalsOfOneHot (keyInputs (packedReader n ρ) state inputHead workHead)) field fallback

theorem packedLookupBit_eval (ρ : Fin (n + decodeGuessWidth n) → Fin a) (input : Basis a)
    (x : Basis n) (g : Basis (decodeGuessWidth n)) (hg : WellCoded g)
    (hρ : input ∘ ρ = Fin.append x g)
    (q : Fin (n+1)) (s : Symbol) (w : Fin n → Symbol)
    (state : Fin (n+1) → BooleanNetwork a 1) (inputHead : Symbol → BooleanNetwork a 1)
    (workHead : Fin n → Symbol → BooleanNetwork a 1)
    (hq : ∀ p, (state p).eval input 0 = decide (q = p))
    (hs : ∀ c, (inputHead c).eval input 0 = decide (s = c))
    (hw : ∀ j c, (workHead j c).eval input 0 = decide (w j = c))
    (field : Fin n → BooleanNetwork a 1) (fallback : Bool) :
    (packedLookupBit ρ state inputHead workHead field fallback).eval input 0 =
      ((firstRow (tableOfBits g) q s w).map (fun i => (field i).eval input 0)).getD fallback :=
  lookupBitNet_eval _ field fallback input (tableOfBits g) q s w
    (keyInputs_agrees (packedReader_agrees ρ input x g hg hρ) state inputHead workHead hq hs hw).keySignals

theorem packedLookupBit_count (ρ : Fin (n + decodeGuessWidth n) → Fin a)
    (state : Fin (n+1) → BooleanNetwork a 1) (inputHead : Symbol → BooleanNetwork a 1)
    (workHead : Fin n → Symbol → BooleanNetwork a 1) {C F : ℕ} (hC : 1 ≤ C)
    (hq : ∀ p, (state p).net.count ≤ C) (hs : ∀ c, (inputHead c).net.count ≤ C)
    (hw : ∀ j c, (workHead j c).net.count ≤ C)
    (field : Fin n → BooleanNetwork a 1) (hf : ∀ i, (field i).net.count ≤ F) (fallback : Bool) :
    (packedLookupBit ρ state inputHead workHead field fallback).net.count ≤
      lookupBitBudget n ((n+3) * (2*((n+1)*(C+4)+1)+5)+1) F := by
  have hr : (packedReader n ρ).Bounded C := fun c v => (packedReader_bounded ρ c v).trans hC
  exact lookupBitNet_count _ field fallback (keyInputs_bounded hr state inputHead workHead hq hs hw).keySignals hf

end SignedProgram.Hot

end SpectralBooks
end LinearAlgebra
end OAI
