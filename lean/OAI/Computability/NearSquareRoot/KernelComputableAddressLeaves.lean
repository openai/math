import OAI.Computability.NearSquareRoot.KernelComputableAddress
import OAI.Computability.NearSquareRoot.KernelComputableDyadic

/-! # Primitive recursive entries of the local binary Walsh and routing leaves -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableAddress

open KernelPass Finset


def rangeProduct (n : ℕ) (f : ℕ → KernelComputableDyadic.Code) : KernelComputableDyadic.Code :=
  n.rec KernelComputableDyadic.one (fun k t => KernelComputableDyadic.mul t (f k))

theorem value_rangeProduct (n : ℕ) (f : ℕ → KernelComputableDyadic.Code) :
    KernelComputableDyadic.value (rangeProduct n f) = ∏ k : Fin n, KernelComputableDyadic.value (f k.val) := by
  induction n with
  | zero => simp [rangeProduct]
  | succ n ih => rw [Fin.prod_univ_castSucc]; simpa only [rangeProduct, Nat.rec_add_one,
      KernelComputableDyadic.value_mul, Fin.val_castSucc, Fin.val_last] using congrArg (· * KernelComputableDyadic.value (f n)) ih

def signBit (s t a : ℕ) : ℕ :=
  ((bitAt s a 0 * bitAt t a 0) % 2 + (bitAt s a 1 * bitAt t a 1) % 2) % 2

def pairCode (s t a : ℕ) : KernelComputableDyadic.Code := if signBit s t a = 0 then KernelComputableDyadic.half else KernelComputableDyadic.negHalf

theorem value_pairCode {A : ℕ} (y x : Column A) (a : Fin A) :
    KernelComputableDyadic.value (pairCode (packColumn A y) (packColumn A x) a) = pairEntry (y a) (x a) := by
  have h : signBit (packColumn A y) (packColumn A x) a =
      (y a 0 * x a 0 + y a 1 * x a 1).val := by
    have bit₀ (t : Column A) : bitAt (packColumn A t) a 0 = (t a 0).val := bitAt_packColumn t a 0
    have bit₁ (t : Column A) : bitAt (packColumn A t) a 1 = (t a 1).val := bitAt_packColumn t a 1
    simp only [signBit, bit₀, bit₁]
    rfl
  simp only [pairCode, h, pairEntry]
  by_cases e : y a 0 * x a 0 + y a 1 * x a 1 = 0
  · simp [e]
  · have ne : (y a 0 * x a 0 + y a 1 * x a 1).val ≠ 0 := fun h => e (Fin.ext h)
    simp [e, ne]

def localChild (A a s t : ℕ) : KernelComputableDyadic.Code :=
  if ∀ z < A, z = a ∨ pairAt s z = pairAt t z then pairCode s t a else KernelComputableDyadic.zero

theorem value_localChild {A : ℕ} (a : Fin A) (y x : Column A) :
    KernelComputableDyadic.value (localChild A a (packColumn A y) (packColumn A x)) = childEntry a y x := by
  have same : (∀ z < A, z = a.val ∨ pairAt (packColumn A y) z = pairAt (packColumn A x) z) ↔
      ∀ z : Fin A, z ≠ a → x z = y z := by
    constructor
    · intro hp z hne
      simpa only [pairAt_packColumn, Fin.val_inj, Equiv.apply_eq_iff_eq] using
        ((hp z.val z.isLt).resolve_left (fun e => hne (Fin.ext e))).symm
    · intro hp z hz
      let k := (⟨z,hz⟩ : Fin A)
      by_cases e : k = a
      · exact Or.inl (congrArg Fin.val e)
      · right
        change pairAt (packColumn A y) k.val = pairAt (packColumn A x) k.val
        rw [pairAt_packColumn, pairAt_packColumn, hp k e]
  simp only [localChild, childEntry, same, apply_ite KernelComputableDyadic.value, value_pairCode, KernelComputableDyadic.value_zero]

def child (A h a y x : ℕ) : KernelComputableDyadic.Code :=
  rangeProduct h (fun c => localChild A a (letter A y c) (letter A x c))

theorem value_child {A h : ℕ} (a : Fin A) (y x : Addr A h) :
    KernelComputableDyadic.value (child A h a (pack A h y) (pack A h x)) = ((Plan.child a).eval h) (0,y) (0,x) := by
  simp only [child, value_rangeProduct, letter_pack, value_localChild, Plan.eval]

def target (A h b i y x : ℕ) : KernelComputableDyadic.Code :=
  if i = b then rangeProduct h (fun c => rangeProduct A
    (fun a => pairCode (letter A y c) (letter A x c) a)) else KernelComputableDyadic.zero

theorem value_target {A h W : ℕ} (b i : Fin W) (y x : Addr A h) :
    KernelComputableDyadic.value (target A h b i (pack A h y) (pack A h x)) = KernelPass.target A W h (b,y) (i,x) := by
  simp [target, KernelPass.target, Fin.val_inj, apply_ite KernelComputableDyadic.value, value_rangeProduct, letter_pack, value_pairCode]

variable {X : Type*} [Primcodable X]

theorem primrec_rangeProduct {n : X → ℕ} {f : X → ℕ → KernelComputableDyadic.Code} (hn : Primrec n) (hf : Primrec₂ f) :
    Primrec (fun x => rangeProduct (n x) (f x)) :=
  Primrec.nat_rec' hn (Primrec.const KernelComputableDyadic.one) (KernelComputableDyadic.primrec_mul.comp (Primrec.snd.comp Primrec.snd)
    (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂

theorem primrec_pairCode {s t a : X → ℕ} (hs : Primrec s) (ht : Primrec t) (ha : Primrec a) :
    Primrec (fun x => pairCode (s x) (t x) (a x)) := by
  have bit (j : ℕ) := Primrec.nat_mod.comp (Primrec.nat_mul.comp (primrec_bitAt hs ha (Primrec.const j))
    (primrec_bitAt ht ha (Primrec.const j))) (Primrec.const 2)
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.nat_add.comp (bit 0) (bit 1))
    (Primrec.const 2)) (Primrec.const 0)) (Primrec.const KernelComputableDyadic.half) (Primrec.const KernelComputableDyadic.negHalf)

theorem primrec_localChild {N a s t : X → ℕ} (hN : Primrec N) (ha : Primrec a)
    (hs : Primrec s) (ht : Primrec t) : Primrec (fun x => localChild (N x) (a x) (s x) (t x)) := by
  have cond : PrimrecRel (fun (z : ℕ) (x : X) => z = a x ∨ pairAt (s x) z = pairAt (t x) z) :=
    (Primrec.eq.comp Primrec.fst (ha.comp Primrec.snd)).or
      (Primrec.eq.comp (primrec_pairAt (hs.comp Primrec.snd) Primrec.fst)
        (primrec_pairAt (ht.comp Primrec.snd) Primrec.fst))
  exact Primrec.ite ((cond.forall_mem_list.comp (Primrec.list_range.comp hN) Primrec.id).of_eq (by simp)) (primrec_pairCode hs ht ha) (Primrec.const KernelComputableDyadic.zero)

theorem primrec_child {A h a y x : X → ℕ} (hA : Primrec A) (hh : Primrec h)
    (ha : Primrec a) (hy : Primrec y) (hx : Primrec x) :
    Primrec (fun u => child (A u) (h u) (a u) (y u) (x u)) :=
  primrec_rangeProduct hh ((primrec_localChild (hA.comp Primrec.fst) (ha.comp Primrec.fst)
    (primrec_letter (hA.comp Primrec.fst) (hy.comp Primrec.fst) Primrec.snd)
    (primrec_letter (hA.comp Primrec.fst) (hx.comp Primrec.fst) Primrec.snd)).to₂)

theorem primrec_target {A h b i y x : X → ℕ} (hA : Primrec A) (hh : Primrec h)
    (hb : Primrec b) (hi : Primrec i) (hy : Primrec y) (hx : Primrec x) :
    Primrec (fun u => target (A u) (h u) (b u) (i u) (y u) (x u)) := by
  have inner := primrec_rangeProduct (hA.comp (Primrec.fst (β := ℕ)))
    (primrec_pairCode ((primrec_letter (hA.comp Primrec.fst) (hy.comp Primrec.fst) Primrec.snd).comp Primrec.fst)
      ((primrec_letter (hA.comp Primrec.fst) (hx.comp Primrec.fst) Primrec.snd).comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.ite (Primrec.eq.comp hi hb) (primrec_rangeProduct hh inner.to₂) (Primrec.const KernelComputableDyadic.zero)

end KernelComputableAddress

end NearSquareRoot
end Computability
end OAI
