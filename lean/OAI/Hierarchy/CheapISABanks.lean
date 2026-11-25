import OAI.Hierarchy.CheapISAWord
import OAI.Computability.VPVNP.RAMMemory
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Compact instruction columns, simulated registers and external RAM -/

namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory
open scoped Fin.CommRing

def columnBase (p : ℕ) (f : Fin 7) := f.val*p
def columnAddr (p : ℕ) (f : Fin 7) (pc : Fin p) := columnBase p f+pc.val
def regBase (p : ℕ) := 7*p
def regAddr {r : ℕ} (p : ℕ) (i : Fin r) := regBase p+i.val
def dataBase (p r : ℕ) := regBase p+r
def dataAddr {w : ℕ} (p r : ℕ) (a : Word w) := dataBase p r+a.val

theorem columnAddr_word {w p : ℕ} (f : Fin 7) (pc : Fin p) :
    (columnAddr p f pc : Word (width w)) = (columnBase p f : Word (width w)) + (pc.val : Word (width w)) :=
  Nat.cast_add ..

theorem regAddr_word {w r : ℕ} (p : ℕ) (i : Fin r) :
    (regAddr p i : Word (width w)) = (regBase p : Word (width w)) + (i.val : Word (width w)) :=
  Nat.cast_add ..

theorem dataAddr_word {w : ℕ} (p r : ℕ) (a : Word w) :
    (dataAddr p r a : Word (width w)) = (dataBase p r : Word (width w)) + wide a :=
  Nat.cast_add ..

theorem column_before {p : ℕ} (f : Fin 7) (pc : Fin p) :
    columnAddr p f pc < regBase p := by
  have col := Nat.mul_le_mul_right p (show f.val+1 ≤ 7 from f.isLt)
  rw [Nat.succ_mul] at col
  unfold columnAddr columnBase regBase
  have row := pc.isLt
  omega

theorem reg_before {p r : ℕ} (i : Fin r) : regAddr p i < dataBase p r :=
  Nat.add_lt_add_left i.isLt _

theorem reg_start {p r : ℕ} (i : Fin r) : regBase p ≤ regAddr p i := Nat.le_add_right ..

theorem data_start {p r w : ℕ} (x : Word w) : dataBase p r ≤ dataAddr p r x := Nat.le_add_right ..

theorem fits_extent {w p r : ℕ} (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1)) :
    dataBase p r+2^w < 2^width w := by
  simp only [pow_succ] at hp hr
  change 7*p+r+2^w < 2^(w+5)
  rw [pow_add,show (2 : ℕ)^5=32 from by decide]
  have pos := Nat.two_pow_pos w
  omega

theorem data_fits {w p r : ℕ} (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1)) (a : Word w) :
    dataAddr p r a < 2^width w :=
  (Nat.add_lt_add_left a.isLt _).trans (fits_extent hp hr)

theorem reg_fits {w p r : ℕ} (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1)) (i : Fin r) :
    regAddr p i < 2^width w :=
  (reg_before i).trans ((Nat.le_add_right ..).trans_lt (fits_extent hp hr))

theorem column_fits {w p r : ℕ} (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1)) (f : Fin 7) (i : Fin p) :
    columnAddr p f i < 2^width w :=
  (column_before f i).trans (((Nat.le_add_right (regBase p) r).trans
    (Nat.le_add_right (dataBase p r) (2^w))).trans_lt (fits_extent hp hr))

/-- The seven instruction fields use untruncated wide words, while the native
register values and original external words are the widened original values. -/
structure Banks {w p r : ℕ} (code : Fin p → Fin 7 → Word (width w))
    (reg : Fin r → Word w) (old : Memory w) (new : Memory (width w)) : Prop where
  exterior (a : Word w) : new (dataAddr p r a) = wide (old a.val)
  register (i : Fin r) : new (regAddr p i) = wide (reg i)
  literal (i : Fin p) (f : Fin 7) : new (columnAddr p f i) = code i f

variable {w p r : ℕ} {code : Fin p → Fin 7 → Word (width w)} {reg : Fin r → Word w}
  {old : Memory w} {new : Memory (width w)}

theorem Banks.putReg (b : Banks code reg old new) (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1))
    (i : Fin r) (v : Word w) :
    Banks code (Function.update reg i v) old
      (writeMemory new (regAddr p i : Word (width w)) (wide v)) := by
  have atWord := Fin.val_cast_of_lt (reg_fits hp hr i)
  constructor
  · intro a
    have ne : dataAddr p r a ≠ regAddr p i := ne_of_gt ((reg_before i).trans_le (data_start a))
    simpa only [writeMemory,atWord,ite_eq_right ne] using b.exterior a
  · intro j
    by_cases same : j = i
    · subst j
      simp [writeMemory,atWord]
    · have ne : regAddr p j ≠ regAddr p i := fun eq => same (Fin.ext (Nat.add_left_cancel eq))
      simpa only [writeMemory,atWord,ite_eq_right ne,Function.update_of_ne same] using b.register j
  · intro pc f
    have ne : columnAddr p f pc ≠ regAddr p i := ne_of_lt ((column_before f pc).trans_le (reg_start i))
    simpa only [writeMemory,atWord,ite_eq_right ne] using b.literal pc f

theorem Banks.putData (b : Banks code reg old new) (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1))
    (a v : Word w) :
    Banks code reg (writeMemory old a v)
      (writeMemory new (dataAddr p r a : Word (width w)) (wide v)) := by
  have atWord := Fin.val_cast_of_lt (data_fits hp hr a)
  constructor
  · intro x
    by_cases same : x.val = a.val
    · have eq := Fin.ext same
      subst x
      simp [writeMemory,atWord]
    · have ne : dataAddr p r x ≠ dataAddr p r a := fun eq => same (Nat.add_left_cancel eq)
      simpa only [writeMemory,atWord,ite_eq_right ne,ite_eq_right same] using b.exterior x
  · intro j
    have ne : regAddr p j ≠ dataAddr p r a := ne_of_lt ((reg_before j).trans_le (data_start a))
    simpa only [writeMemory,atWord,ite_eq_right ne] using b.register j
  · intro pc f
    have start : regBase p ≤ dataAddr p r a := (Nat.le_add_right (regBase p) r).trans (data_start a)
    have ne : columnAddr p f pc ≠ dataAddr p r a := ne_of_lt ((column_before f pc).trans_le start)
    simpa only [writeMemory,atWord,ite_eq_right ne] using b.literal pc f

/-- ROM first, then zero registers and the original caller's header. -/
def bankHeader (r : ℕ) (code : Fin p → Fin 7 → Word (width w)) (header : ℕ → Word w) (j : ℕ) :
    Word (width w) :=
  if rom : j < regBase p then
    have hp : 0 < p := Nat.pos_of_ne_zero (fun h => by simp [regBase,h] at rom)
    code ⟨j%p,Nat.mod_lt _ hp⟩ ⟨j/p,(Nat.div_lt_iff_lt_mul hp).2 rom⟩
  else if j < dataBase p r then 0 else wide (header (j-dataBase p r))

theorem initial_banks (code : Fin p → Fin 7 → Word (width w)) (r S : ℕ) (header : ℕ → Word w) :
    Banks code (fun _ : Fin r => 0) (initialMemory S header)
      (initialMemory (dataBase p r+S) (bankHeader r code header)) := by
  constructor
  · intro a
    have nrom : ¬dataAddr p r a < regBase p := not_lt_of_ge
      ((Nat.le_add_right (regBase p) r).trans (data_start a))
    have nreg := not_lt_of_ge (data_start (p := p) (r := r) a)
    by_cases low : a.val < S
    · have placed : dataAddr p r a < dataBase p r+S := Nat.add_lt_add_left low _
      simp only [initialMemory,ite_eq_left placed,ite_eq_left low,bankHeader,dite_eq_right nrom,ite_eq_right nreg]
      simp [dataAddr]
    · have beyond : ¬dataAddr p r a < dataBase p r+S := fun h => low (Nat.lt_of_add_lt_add_left h)
      simp [initialMemory,beyond,low]
  · intro i
    have hi := reg_before (p := p) i
    have nrom := not_lt_of_ge (reg_start (p := p) i)
    have within := hi.trans_le (Nat.le_add_right (dataBase p r) S)
    simp [initialMemory,bankHeader,within,nrom,hi]
  · intro i f
    have hi := column_before f i
    have within := hi.trans_le ((Nat.le_add_right (regBase p) r).trans (Nat.le_add_right (dataBase p r) S))
    simp only [initialMemory,ite_eq_left within,bankHeader,dite_eq_left hi]
    congr 1
    · apply Fin.ext
      exact Nat.mul_add_mod_of_lt i.isLt
    · apply Fin.ext
      change (f.val*p+i.val)/p=f.val
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt i.isLt),Nat.div_eq_of_lt i.isLt,
        Nat.zero_add]

end Hierarchy.CheapISA

end OAI
