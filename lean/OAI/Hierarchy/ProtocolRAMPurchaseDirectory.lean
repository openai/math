import OAI.Hierarchy.ProtocolRAMPurchaseDFS
import OAI.Hierarchy.ProtocolRAMScan
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Public address rows for the padded sampler DFS

Only a starting ordinal and a list of branch digits are installed. These
words depend on the row count, the sampler degree and the fixed path length.
-/

namespace Hierarchy.ProtocolRAM.PurchaseDirectory
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {n D h w : ℕ}

abbrev Index (n D h : ℕ) := Fin (PurchaseDFS.layout n D h).length

def item (i : Index n D h) := (PurchaseDFS.layout n D h).get i

def bits (n D h : ℕ) := Nat.log 2 (n*D^h+1)+1

def span (n D h : ℕ) := 2^bits n D h

theorem rows_lt_span : n*D^h < span n D h :=
  (Nat.lt_succ_self _).trans (Nat.lt_pow_succ_log_self (by decide) _)

theorem span_le : span n D h ≤ 2*(n*D^h+1) := by
  simpa [span,bits,pow_succ,Nat.mul_comm] using
    Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (Nat.succ_ne_zero (n*D^h)))

def bank (base n D h lane : ℕ) : Bank := ⟨base+lane*span n D h,bits n D h⟩

def value (n D h lane row : ℕ) : ℕ :=
  if hi : row < (PurchaseDFS.layout n D h).length then
    let x := item (n:=n) (D:=D) (h:=h) ⟨row,hi⟩
    match lane with
    | 0 => x.1.val+1
    | j+1 => if hj:j<h then (x.2 ⟨j,hj⟩).val else 0
  else 0

/-- The image occupies `(h+1)*span` words, including padding to power-of-two bank sizes. -/
def install (base n D h : ℕ) (m : Memory w) : Memory w :=
  fillSegment base ((h+1)*span n D h) (fun a =>
    (value n D h ((a-base)/span n D h) ((a-base)%span n D h) : Word w)) m

structure Loaded (base n D h : ℕ) (m : Memory w) : Prop where
  start : ∀ i : Index n D h, (bank base n D h 0).read m (i.val : Word w) = ((item i).1.val+1 : ℕ)
  digit : ∀ (i : Index n D h) (d : Fin h),
    (bank base n D h (d.val+1)).read m (i.val:Word w) = ((item i).2 d).val

private theorem read_install (base : ℕ) (m : Memory w) (space : (PurchaseDFS.layout n D h).length ≤ 2^w)
    (i : Index n D h) (lane : Fin (h+1)) :
    (bank base n D h lane.val).read (install base n D h m) (i.val : Word w) =
      (value n D h lane.val i.val : Word w) := by
  have ir : i.val < span n D h := i.isLt.trans (by simpa using (rows_lt_span (n:=n) (D:=D) (h:=h)))
  have divide : (lane.val*span n D h+i.val)/span n D h=lane.val := by
    rw [Nat.mul_comm lane.val, Nat.mul_add_div (show 0 < span n D h from Nat.two_pow_pos _),Nat.div_eq_of_lt ir,Nat.add_zero]
  have offset : lane.val*span n D h+i.val < (h+1)*span n D h := by
    have next := Nat.mul_le_mul_right (span n D h) lane.isLt
    rw [Nat.succ_mul] at next
    exact (Nat.add_lt_add_left ir _).trans_le next
  change install base n D h m (base+lane.val*span n D h+(i.val:Word w).val%span n D h) = _
  rw [Fin.val_cast_of_lt (i.isLt.trans_le space),Nat.mod_eq_of_lt ir]
  have inside : base≤base+lane.val*span n D h+i.val ∧
      base+lane.val*span n D h+i.val<base+(h+1)*span n D h := by omega
  simp only [install,fillSegment,ite_eq_left inside]
  rw [Nat.add_assoc,Nat.add_sub_cancel_left,divide,Nat.mul_add_mod',Nat.mod_eq_of_lt ir]

theorem install_loaded (base : ℕ) (m : Memory w) (space : (PurchaseDFS.layout n D h).length ≤ 2^w) :
    Loaded base n D h (install base n D h m) := by
  have bound (i : Index n D h) : i.val < n * D ^ h := by simpa using i.isLt
  constructor
  · intro i
    simpa [value,i.isLt,bound i] using read_install base m space i (0 : Fin (h+1))
  · intro i d
    simpa [value,i.isLt,bound i,d.isLt] using read_install base m space i d.succ

theorem frame (base n D h : ℕ) (m : Memory w) (a : ℕ)
    (outside : a<base ∨ base+(h+1)*span n D h ≤ a) : install base n D h m a=m a := by
  simp [install,fillSegment,show ¬(base≤a ∧ a<base+(h+1)*span n D h) by omega]

theorem Loaded.of_frame {base : ℕ} {m m' : Memory w} (load : Loaded base n D h m)
    (stable : ∀ a, base ≤ a → a < base+(h+1)*span n D h → m' a=m a) : Loaded base n D h m' := by
  have same (lane : Fin (h+1)) (i : Word w) :
      (bank base n D h lane.val).read m' i = (bank base n D h lane.val).read m i := by
    apply stable
    · change base ≤ base+lane.val*span n D h+i.val%span n D h
      omega
    · change base+lane.val*span n D h+i.val%span n D h < base+(h+1)*span n D h
      have next := Nat.mul_le_mul_right (span n D h) lane.isLt
      have rem := Nat.mod_lt i.val (Nat.two_pow_pos (bits n D h))
      change i.val%span n D h < span n D h at rem
      rw [Nat.succ_mul] at next
      omega
  exact ⟨fun i => (same 0 _).trans (load.start i),fun i j => (same j.succ _).trans (load.digit i j)⟩

end Hierarchy.ProtocolRAM.PurchaseDirectory

end OAI
