import OAI.ThreeFlat.RAM.HistoryFactorScan
import OAI.ThreeFlat.RAM.HistoryFactorLibrary
import OAI.ThreeFlat.RAM.ContractionLookup

namespace OAI
/-! # Four-word trivalent factor descriptors with a shared coefficient library -/

namespace ThreeFlat.RAM.HistoryFactors

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM BitLayout Contraction Fin.CommRing

variable {F : Type*} {p w : ℕ}

/-- Row addressing in a bounded packed word array. -/
private theorem load {m : Memory w} (b stride i j : ℕ) (fit : b+stride*i+j < 2^w) :
    m (BinaryOp.eval .add (BinaryOp.eval .add (b : Word w)
      (BinaryOp.eval .mul (stride : Word w) (i : Word w))) (j : Word w)).val =
      m (b+stride*i+j) := by
  change m (((b : Word w) + (stride : Word w) * (i : Word w) + (j : Word w)).val) = _
  rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Fin.val_cast_of_lt fit]

private theorem sub_start (a offset : ℕ) :
    BinaryOp.eval .sub ((a+offset : ℕ) : Word w) (a : Word w) = (offset : Word w) := by
  change _ - _ = _
  rw [Nat.cast_add]
  abel

private theorem div_mod {i j : ℕ} (hj : j < 11) (bounded : 11*i+j < 2^w)
    (wide : 11 < 2^w) :
    BinaryOp.eval .div ((11*i+j : ℕ) : Word w) 11 = (i : Word w) ∧
      BinaryOp.eval .mod ((11*i+j : ℕ) : Word w) 11 = (j : Word w) := by
  have eleven : (11 : Word w).val = 11 :=
    show 11 % 2^w = 11 from Nat.mod_eq_of_lt wide
  simp only [BinaryOp.eval, Fin.val_cast_of_lt bounded, eleven]
  rw [show (11*i+j)/11 = i by omega, show (11*i+j)%11 = j by omega]
  exact ⟨rfl,rfl⟩

variable [Fintype F] [Field F]

/-- Executing the compact lookup returns the source word or coefficient in the
expanded cell record, with every accessed live table address inside the word space. -/
theorem read_record_eq (N : BitNetwork F p) (fit : Fits N w) (L : Library N)
    (code : FieldCode F w) (metadata lut : ℕ) (m : Memory w)
    (hmeta : metadata+4*N.cells ≤ 2^w) (hlut : lut+8*L.count ≤ 2^w)
    (stored : Stores N L code metadata lut m) (i : Fin N.cells) (j : Fin 11) :
    HistoryFactorScan.readWord (cellsBase p N.internal : Word w) (metadata : Word w)
      (lut : Word w) ((cellsBase p N.internal + 11*i.val+j.val : ℕ) : Word w) m =
      record N code i j := by
  have hlast := cellAddr_lt N fit i.isLt
  have hcell := cell_offset_lt N fit i j.isLt
  have hj := j.isLt
  have hi := i.isLt
  have hdelta : 11*i.val+j.val < 2^w := by unfold cellAddr at hcell; omega
  have wide : 11 < 2^w := by unfold cellAddr cellsBase hiddenBase at hlast; omega
  obtain ⟨hr,hc⟩ := div_mod hj hdelta wide
  have hthree : (3 : Word w).val = 3 :=
    show 3 % 2^w = 3 from Nat.mod_eq_of_lt (by omega)
  have hcol : ((j.val : Word w) : ℕ) = j.val := Fin.val_cast_of_lt (by omega)
  have test : ((j.val : Word w) < 3) ↔ j.val < 3 := by
    change ((j.val : Word w) : ℕ) < (3 : Word w).val ↔ _
    rw [hcol,hthree]
  unfold HistoryFactorScan.readWord
  simp only [Nat.add_assoc (cellsBase p N.internal), sub_start, hr, hc, test]
  by_cases h : j.val < 3
  · rw [ite_eq_left h, record, dite_eq_left h]
    exact (load (m := m) metadata 4 i.val j.val (by omega)).trans (stored.source i ⟨_,h⟩)
  · rw [ite_eq_right h, record, dite_eq_right h]
    have tag : m (BinaryOp.eval .add (BinaryOp.eval .add (metadata : Word w)
          (BinaryOp.eval .mul 4 (i.val : Word w))) 3).val = ((L.id i).val : Word w) :=
      (load (m := m) metadata 4 i.val 3 (by omega)).trans (stored.tag i)
    have offset : BinaryOp.eval .sub (j.val : Word w) 3 = ((j.val - 3 : ℕ) : Word w) := by
      change (j.val : Word w) - 3 = _
      rw [Nat.cast_sub (by omega : 3 ≤ j.val)]; rfl
    rw [tag,offset,L.correct]
    exact (load (m := m) lut 8 (L.id i).val (j.val-3) (by have := (L.id i).isLt; omega)).trans
      (stored.coefficient (L.id i) ⟨_,by omega⟩)

end ThreeFlat.RAM.HistoryFactors

end OAI
