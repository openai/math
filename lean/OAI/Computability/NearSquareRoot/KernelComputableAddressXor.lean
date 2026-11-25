import OAI.Computability.NearSquareRoot.KernelComputableAddress
import OAI.Computability.NearSquareRoot.KernelComputableDyadic

/-! # Uniform arithmetic reindexing for a binary XOR pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableAddress
open KernelPass Finset

def assemble (b n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ range n, f i * b^i

theorem assemble_eq {b n : ℕ} (v : Fin n → Fin b) (f : ℕ → ℕ)
    (hf : ∀ k : Fin n, f k.val = (v k).val) :
    assemble b n f = (finFunctionFinEquiv v).val := by
  rw [assemble, ← Fin.sum_univ_eq_sum_range, finFunctionFinEquiv_apply]
  simp [hf]

def changeBit (a b t r j : ℕ) : ℕ :=
  if a ≠ b ∧ r = a then (bitAt t r j + bitAt t b j) % 2 else bitAt t r j

def changeColumn (A a b t : ℕ) : ℕ :=
  assemble 4 A fun r => assemble 2 2 fun j => changeBit a b t r j

theorem changeColumn_pack {A : ℕ} (a b : Fin A) (x : Column A) :
    changeColumn A a b (packColumn A x) = (packColumn A (xorColumn (a,b) x)).val := by
  apply assemble_eq (fun r => packSig 2 (xorColumn (a,b) x r))
  intro r
  apply assemble_eq (xorColumn (a,b) x r)
  intro j
  simp only [changeBit, bitAt_packColumn, ne_eq, Fin.val_inj, xorColumn]
  by_cases h : a ≠ b ∧ r = a <;> simp only [h, ite_false] <;> rfl

def xorAddress (A h a b x : ℕ) : ℕ :=
  assemble (4^A) h (fun c => changeColumn A a b (letter A x c))

theorem xorAddress_pack {A h : ℕ} (a b : Fin A) (x : Addr A h) :
    xorAddress A h a b (pack A h x) = (pack A h (xorColumn (a,b) ∘ x)).val := by
  apply assemble_eq (fun c => packColumn A (xorColumn (a,b) (x c)))
  intro c
  rw [letter_pack, changeColumn_pack]

def xorEntry (A h a b y x : ℕ) : KernelComputableDyadic.Code :=
  if y = xorAddress A h a b x then KernelComputableDyadic.one else KernelComputableDyadic.zero

theorem value_xorEntry {A h : ℕ} (a b : Fin A) (y x : Addr A h) :
    KernelComputableDyadic.value (xorEntry A h a b (pack A h y) (pack A h x)) =
      ((Plan.xor (a,b)).eval h) (0,y) (0,x) := by
  simp [xorEntry, xorAddress_pack, Fin.val_inj, apply_ite KernelComputableDyadic.value, Plan.eval]

variable {X : Type*} [Primcodable X]

theorem primrec_assemble {b n : X → ℕ} {f : X → ℕ → ℕ}
    (hb : Primrec b) (hn : Primrec n) (hf : Primrec₂ f) :
    Primrec (fun x => assemble (b x) (n x) (f x)) :=
  primrec_rangeSum hn (Primrec.nat_mul.comp hf (primrec_pow (hb.comp Primrec.fst) Primrec.snd)).to₂

theorem primrec_changeBit {a b t r j : X → ℕ} (ha : Primrec a) (hb : Primrec b) (ht : Primrec t)
    (hr : Primrec r) (hj : Primrec j) : Primrec (fun x => changeBit (a x) (b x) (t x) (r x) (j x)) :=
  Primrec.ite ((Primrec.eq.comp ha hb).not.and (Primrec.eq.comp hr ha))
    (Primrec.nat_mod.comp (Primrec.nat_add.comp (primrec_bitAt ht hr hj) (primrec_bitAt ht hb hj))
      (Primrec.const 2)) (primrec_bitAt ht hr hj)

theorem primrec_changeColumn {A a b t : X → ℕ} (hA : Primrec A) (ha : Primrec a) (hb : Primrec b)
    (ht : Primrec t) : Primrec (fun x => changeColumn (A x) (a x) (b x) (t x)) := by
  have inner := primrec_assemble (Primrec.const 2) (Primrec.const 2)
    (primrec_changeBit ((ha.comp Primrec.fst).comp Primrec.fst)
    ((hb.comp Primrec.fst).comp Primrec.fst) ((ht.comp Primrec.fst).comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact primrec_assemble (Primrec.const 4) hA inner.to₂

theorem primrec_xorAddress {A h a b t : X → ℕ} (hA : Primrec A) (hh : Primrec h)
    (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) :
    Primrec (fun x => xorAddress (A x) (h x) (a x) (b x) (t x)) :=
  primrec_assemble (primrec_pow (Primrec.const 4) hA) hh
    (primrec_changeColumn (hA.comp Primrec.fst) (ha.comp Primrec.fst) (hb.comp Primrec.fst)
      (primrec_letter (hA.comp Primrec.fst) (ht.comp Primrec.fst) Primrec.snd)).to₂

theorem primrec_xorEntry {A h a b y x : X → ℕ} (hA : Primrec A) (hh : Primrec h)
    (ha : Primrec a) (hb : Primrec b) (hy : Primrec y) (hx : Primrec x) :
    Primrec (fun t => xorEntry (A t) (h t) (a t) (b t) (y t) (x t)) :=
  Primrec.ite (Primrec.eq.comp hy (primrec_xorAddress hA hh ha hb hx))
    (Primrec.const _) (Primrec.const _)

end KernelComputableAddress

end NearSquareRoot
end Computability
end OAI
