import OAI.Hierarchy.ProtocolRAMGateColumnCore
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Explicit immutable shape directory for the native purchase-gate compiler -/

namespace Hierarchy.ProtocolRAM.GateColumns

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

/-- The least information needed for each gate is public: is this operand a
constant address, and if not which earlier word holds the tile ID? -/
def publicWord {n : ℕ} (spec : Fin n → Fin 3 → Operand) (col : Fin 6) (row : Fin n) : ℕ :=
  let c : Fin 3 := ⟨col.val/2,by omega⟩
  if col.val%2=0 then (spec row c).mode else (spec row c).argument

/-- The word at a relative address in the six-column public tape. Padding is zero. -/
def directoryWord {n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand) (a : ℕ) : ℕ :=
  if h : a/D.stride<6 ∧ a%D.stride<n then
    publicWord spec ⟨a/D.stride,h.1⟩ ⟨a%D.stride,h.2⟩
  else 0

/-- The possible contents of the public tape are specified by a finite list, with no
reference to runtime memory. -/
def adviceWords {n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand) :=
  List.ofFn (fun a : Fin (6*D.stride) => directoryWord D spec a.val)

@[simp] theorem adviceWords_length {n : ℕ} (D : Directory) (s : Fin n → Fin 3 → Operand) :
    (adviceWords D s).length = 6*D.stride := by simp [adviceWords]

def mount {w n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand) (m : Memory w) : Memory w :=
  fun a => if D.base≤a ∧ a<D.base+6*D.stride then (directoryWord D spec (a-D.base) : Word w) else m a

theorem mount_frame {w n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand) (m : Memory w)
    {a : ℕ} (outside : a < D.base ∨ D.base+6*D.stride≤a) : mount D spec m a=m a := by
  exact ite_eq_right (show ¬(D.base≤a ∧ a<D.base+6*D.stride) by omega)

theorem mount_adviceWord {w n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand)
    (m : Memory w) (a : Fin (6*D.stride)) :
    mount D spec m (D.base+a.val)=((adviceWords D spec)[a.val]'(by simp) : Word w) := by
  have h : D.base+a.val<D.base+6*D.stride := by omega
  simp [mount,h,adviceWords]

theorem read_column {w n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand) (m : Memory w)
    (cap : n≤D.stride) (room : D.stride<2^w) (j : Fin 6) (i : Fin n) :
    (D.bank j.val).read (mount D spec m) (i.val : Word w) = (publicWord spec j i : Word w) := by
  have stride : 0<D.stride := Nat.two_pow_pos _
  have lt := i.isLt.trans_le cap
  have addr : D.base≤D.base+j.val*D.stride+i.val ∧ D.base+j.val*D.stride+i.val<D.base+6*D.stride := by
    have next : (j.val+1)*D.stride≤6*D.stride := Nat.mul_le_mul_right _ j.isLt
    rw [Nat.succ_mul] at next
    omega
  have idx : D.base+j.val*D.stride+i.val-D.base=j.val*D.stride+i.val := by omega
  have divi : (j.val*D.stride+i.val)/D.stride=j.val := by
    rw [Nat.mul_comm j.val D.stride,Nat.mul_add_div stride,Nat.div_eq_of_lt lt,Nat.add_zero]
  have modi : (j.val*D.stride+i.val)%D.stride=i.val := by simp [Nat.mod_eq_of_lt lt]
  simp only [Bank.read,Fin.val_cast_of_lt (lt.trans room),Directory.bank,Bank.size]
  change mount D spec m (D.base+j.val*D.stride+i.val%D.stride) = _
  simp [Nat.mod_eq_of_lt lt,mount,addr,idx,directoryWord,divi,modi,j.isLt,i.isLt]

theorem mount_mounted {w n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand) (m : Memory w)
    (cap : n≤D.stride) (room : D.stride<2^w) : Mounted D spec (mount D spec m) := by
  intro i c
  have j1 : 2*c.val<6 := by omega
  have j2 : 2*c.val+1<6 := by omega
  constructor
  · simpa [publicWord] using read_column D spec m cap room ⟨2*c.val,j1⟩ i
  · have quo : (2*c.val+1)/2=c.val := by omega
    have rem : (2*c.val+1)%2=1 := by omega
    simpa [publicWord,quo,rem] using read_column D spec m cap room ⟨2*c.val+1,j2⟩ i

/-- The DFS phase may update arbitrary live RAM. Preserving the six directory banks
at their actual addresses preserves the static gate recipes. -/
theorem mounted_of_frame {w n : ℕ} (D : Directory) (spec : Fin n → Fin 3 → Operand)
    {m m' : Memory w} (before : Mounted D spec m)
    (frame : ∀ a, D.base≤a → a<D.base+6*D.stride → m' a=m a) : Mounted D spec m' := by
  have eq (c : ℕ) (hc : c<6) (i : Word w) : (D.bank c).read m' i=(D.bank c).read m i := by
    apply frame
    · change D.base ≤ D.base+c*D.stride+i.val%D.stride
      omega
    · change D.base+c*D.stride+i.val%D.stride<D.base+6*D.stride
      have next := Nat.mul_le_mul_right D.stride hc
      rw [Nat.succ_mul] at next
      have := Nat.mod_lt i.val (Nat.two_pow_pos D.bits)
      change i.val%D.stride < D.stride at this
      omega
  intro i c
  exact ⟨(eq _ (by omega) _).trans (before i c).1,(eq _ (by omega) _).trans (before i c).2⟩

def directory (base n : ℕ) : Directory := ⟨base,Nat.log 2 (n+1)+1⟩

theorem directory_capacity (base n : ℕ) : n≤(directory base n).stride := by
  exact n.le_succ.trans (Nat.lt_pow_succ_log_self (by decide : 1<2) (n+1)).le

theorem directory_space (base n : ℕ) : 6*(directory base n).stride ≤ 12*(n+1) := by
  have t := Nat.pow_log_le_self 2 (show n+1 ≠ 0 by omega)
  simp only [directory,Directory.stride,pow_succ]
  omega

end Hierarchy.ProtocolRAM.GateColumns

end OAI
