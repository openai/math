import OAI.Computability.NearSquareRoot.KernelComputableAddress
import OAI.Computability.NearSquareRoot.KernelComputableDyadicCoefficient

/-! # Primitive recursive evaluation of binary parity-table passes

A column selects a natural-number mask. The parity of a fixed position in
these masks gives one bit of the index for the coefficient table. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableSelector

open KernelPass KernelComputableAddress Finset
open KernelComputableDyadic (Code)

def test (A q : ℕ) (masks : List ℕ) (c : Column A) (j : Fin q) : ZMod 2 :=
  (digit 2 (masks.getD (packColumn A c).val 0) j.val : ℕ)

def parity (A h : ℕ) (masks : List ℕ) (x j : ℕ) : ℕ :=
  (∑ c ∈ range h, digit 2 (masks.getD (letter A x c) 0) j) % 2

def index (A h q : ℕ) (masks : List ℕ) (x : ℕ) : ℕ :=
  ∑ j ∈ range q, parity A h masks x j * 2^j

def entry (A h q : ℕ) (masks : List ℕ) (values : List Code) (y x : ℕ) : Code :=
  if x = y then values.getD (index A h q masks x) KernelComputableDyadic.zero else KernelComputableDyadic.zero

def table {q : ℕ} (values : List Code) (s : Fin q → ZMod 2) : Coefficient :=
  KernelComputableDyadic.coefficient (values.getD (packSig q s).val KernelComputableDyadic.zero)

theorem parity_pack {A h q : ℕ} (masks : List ℕ) (x : Addr A h) (j : Fin q) :
    parity A h masks (pack A h x) j = ((∑ c, test A q masks (x c)) j).val := by
  unfold parity
  rw [← Fin.sum_univ_eq_sum_range, ← ZMod.val_natCast]
  simp only [letter_pack, Nat.cast_sum, Finset.sum_apply, test]

theorem index_pack {A h q : ℕ} (masks : List ℕ) (x : Addr A h) :
    index A h q masks (pack A h x) = (packSig q (∑ c, test A q masks (x c))).val := by
  let f : Fin q → Fin 2 := ∑ c, test A q masks (x c)
  have eq := finFunctionFinEquiv_apply f
  apply Eq.trans _ eq.symm
  rw [index, ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl (fun j _ => congrArg (· * 2^j.val) (parity_pack _ _ j))

theorem entry_eval {A h q : ℕ} (masks : List ℕ) (vs : List Code) (y x : Addr A h) :
    KernelComputableDyadic.value (entry A h q masks vs (pack A h y) (pack A h x)) =
      (Plan.scale q (test A q masks) (table vs)).eval h (0,y) (0,x) := by
  by_cases he : x = y
  · subst y
    simp only [entry, ite_true, index_pack, Plan.eval, table, KernelComputableDyadic.value_coefficient]
  · have hn : (pack A h x).val ≠ (pack A h y).val := fun t => he ((pack A h).injective (Fin.ext t))
    simp [entry, hn, Plan.eval, he, KernelComputableDyadic.value, KernelComputableDyadic.zero]

def encodeTests {A q : ℕ} (f : Column A → Fin q → ZMod 2) : List ℕ :=
  List.ofFn fun k : Fin (4^A) => (packSig q (f ((packColumn A).symm k))).val

theorem test_encode {A q : ℕ} (f : Column A → Fin q → ZMod 2) : test A q (encodeTests f) = f := by
  funext c j
  simp [test, encodeTests, List.getD, digit_packSig]

def encodeTable {q : ℕ} (f : (Fin q → ZMod 2) → Coefficient) : List Code :=
  List.ofFn fun k : Fin (2^q) => KernelComputableDyadic.ofCoefficient (f ((packSig q).symm k))

theorem table_encode {q : ℕ} (f : (Fin q → ZMod 2) → Coefficient) : table (encodeTable f) = f := by
  funext x
  simp [table, encodeTable, List.getD]

variable {X : Type*} [Primcodable X]

theorem primrec_parity {A h x j : X → ℕ} {masks : X → List ℕ}
    (hA : Primrec A) (hh : Primrec h) (hM : Primrec masks) (hx : Primrec x) (hj : Primrec j) :
    Primrec fun u => parity (A u) (h u) (masks u) (x u) (j u) :=
  Primrec.nat_mod.comp (primrec_rangeSum hh ((primrec_digit (Primrec.const 2)
    ((Primrec.list_getD 0).comp (hM.comp Primrec.fst)
      (primrec_letter (hA.comp Primrec.fst) (hx.comp Primrec.fst) Primrec.snd))
    (hj.comp Primrec.fst)).to₂)) (Primrec.const 2)

theorem primrec_index {A h q x : X → ℕ} {masks : X → List ℕ}
    (hA : Primrec A) (hh : Primrec h) (hq : Primrec q) (hM : Primrec masks) (hx : Primrec x) :
    Primrec fun u => index (A u) (h u) (q u) (masks u) (x u) :=
  primrec_rangeSum hq (Primrec.nat_mul.comp
    (primrec_parity (hA.comp Primrec.fst) (hh.comp Primrec.fst) (hM.comp Primrec.fst)
      (hx.comp Primrec.fst) Primrec.snd) (primrec_pow (Primrec.const 2) Primrec.snd)).to₂

theorem primrec_entry {A h q x y : X → ℕ} {masks : X → List ℕ} {vs : X → List Code}
    (hA : Primrec A) (hh : Primrec h) (hq : Primrec q) (hM : Primrec masks)
    (hV : Primrec vs) (hy : Primrec y) (hx : Primrec x) :
    Primrec fun u => entry (A u) (h u) (q u) (masks u) (vs u) (y u) (x u) :=
  Primrec.ite (Primrec.eq.comp hx hy)
    ((Primrec.list_getD KernelComputableDyadic.zero).comp hV (primrec_index hA hh hq hM hx)) (Primrec.const KernelComputableDyadic.zero)

end KernelComputableSelector

end NearSquareRoot
end Computability
end OAI
