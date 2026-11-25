import OAI.Hierarchy.GridPassageRAMStep
import OAI.Hierarchy.GridRailNumeric

namespace OAI
/-! # Native decoding of a rail and a cell-direction counter -/

namespace Hierarchy.GridPassageRAMRow
open Computability.VPVNP.BurstRAM PrivateRAM GridLens
open scoped Fin.CommRing

variable {w k n : ℕ}

def cursor (e : ℕ) (t : Fin (n+1)) : ℕ := e*(n+1)+t.val

def bucket (d : Fin k) (row : Fin k → Fin (n+1)) (t : Fin (n+1)) : ℕ :=
  (finFunctionFinEquiv (cellOnRail d row t)).val*k + d.val

/-- The sentinel is the radix, one past the last longitudinal coordinate. -/
def tag (h : Option (Fin (n+1))) : ℕ := h.elim (n+1) Fin.val

structure DecodeReads (m : Memory w) (dirBase cellBase powerBase touchBase e : ℕ)
    (d : Fin k) (row : Fin k → Fin (n+1)) (h : Option (Fin (n+1))) : Prop where
  dir : m (dirBase+e) = (d.val : Word w)
  rep : m (cellBase+e) = ((finFunctionFinEquiv row).val : Word w)
  power : m (powerBase+d.val) = (((n+1)^d.val : ℕ) : Word w)
  touch : m (touchBase+e) = (tag h : Word w)

structure DecodeRoom (w dirBase cellBase powerBase touchBase e : ℕ)
    (d : Fin k) (_row : Fin k → Fin (n+1)) (t : Fin (n+1)) : Prop where
  radix : n+1 < 2^w
  cursor : GridPassageRAMRow.cursor e t < 2^w
  extent : (n+1)^k < 2^w
  dir : dirBase+e < 2^w
  cell : cellBase+e < 2^w
  power : powerBase+d.val < 2^w
  touch : touchBase+e < 2^w

theorem address_val (a b : ℕ) (room : a+b < 2^w) :
    ((a : Word w)+(b : Word w)).val = a+b := by
  rw [← Nat.cast_add, Fin.val_cast_of_lt room]

theorem divWord_cast (a b : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    BinaryOp.div.eval (a : Word w) (b : Word w) = ((a/b : ℕ) : Word w) := by
  change Fin.ofNat _ ((a : Word w).val / (b : Word w).val) = _
  rw [Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb]; rfl

theorem modWord_cast (a b : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    BinaryOp.mod.eval (a : Word w) (b : Word w) = ((a%b : ℕ) : Word w) := by
  change Fin.ofNat _ ((a : Word w).val % (b : Word w).val) = _
  rw [Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb]; rfl

private theorem tag_eq (h : Option (Fin (n+1))) (t : Fin (n+1)) (room : n+1 < 2^w) :
    (tag h : Word w) = (t.val : Word w) ↔ h = some t := by
  have fits : tag h < 2^w := by
    cases h with
    | none => exact room
    | some s => exact s.isLt.trans room
  constructor
  · intro same
    have eqn := congrArg Fin.val same
    rw [Fin.val_cast_of_lt fits, Fin.val_cast_of_lt (t.isLt.trans room)] at eqn
    cases h with
    | none =>
      change n+1=t.val at eqn
      exact False.elim ((Nat.ne_of_gt t.isLt) eqn)
    | some s => exact congrArg some (Fin.ext eqn)
  · rintro rfl
    rfl

/-- The RAM row reads all four geometry pages, replaces the correct radix
digit in the representative ordinal, and executes the natural table step. -/
theorem decode_step (limit B dirBase cellBase powerBase touchBase C O M scratch e : ℕ)
    (d : Fin k) (row : Fin k → Fin (n+1)) (t : Fin (n+1)) (h : Option (Fin (n+1)))
    (m : Memory w) (reads : DecodeReads m dirBase cellBase powerBase touchBase e d row h)
    (room : DecodeRoom w dirBase cellBase powerBase touchBase e d row t)
    (capFit : B < 2^w) (countFit : C+bucket d row t < 2^w)
    (markFit : M+cursor e t < 2^w)
    (destFit : decide (h ≠ some t) = true ∧ (m (C+bucket d row t)).val < B →
      O+bucket d row t*B+(m (C+bucket d row t)).val < 2^w) :
    wordStep (values w limit (n+1) k B dirBase cellBase powerBase touchBase C O M scratch)
        (cursor e t : Word w) m =
      natStep C O M B (bucket d row t) e (cursor e t) (decide (h ≠ some t)) m := by
  let v := values w limit (n+1) k B dirBase cellBase powerBase touchBase C O M scratch
  let g := n+1
  let a := (finFunctionFinEquiv row).val
  let s := g^d.val
  have gAt : v 1 = (g : Word w) := rfl
  have kAt : v 2 = (k : Word w) := rfl
  have dirAt : v 4 = (dirBase : Word w) := rfl
  have cellAt : v 5 = (cellBase : Word w) := rfl
  have powerAt : v 6 = (powerBase : Word w) := rfl
  have touchAt : v 7 = (touchBase : Word w) := rfl
  have quotient : cursor e t / g = e := by
    change (e*(n+1)+t.val)/(n+1)=e
    rw [Nat.mul_comm e (n+1), Nat.mul_add_div (Nat.succ_pos _), Nat.div_eq_of_lt t.isLt,
      Nat.add_zero]
  have remainder : cursor e t % g = t.val := by simp [cursor,g,Nat.mod_eq_of_lt t.isLt]
  have af : a < 2^w := (finFunctionFinEquiv row).isLt.trans room.extent
  have sf : s < 2^w :=
    (Nat.pow_le_pow_right (Nat.succ_pos n) d.isLt.le).trans_lt room.extent
  have rail := (divWord_cast (cursor e t) g room.cursor room.radix).trans
    (congrArg (fun z : ℕ => (z : Word w)) quotient)
  have position := (modWord_cast (cursor e t) g room.cursor room.radix).trans
    (congrArg (fun z : ℕ => (z : Word w)) remainder)
  have digit := modWord_cast (a/s) g ((Nat.div_le_self ..).trans_lt af) room.radix
  have erase : (a/s%g)*s ≤ a := (Nat.mul_le_mul_right s (Nat.mod_le (a/s) g)).trans
    (Nat.div_mul_le_self a s)
  have key : ((a : Word w) - ((a/s%g : ℕ) : Word w)*(s : Word w) +
      (t.val : Word w)*(s : Word w))*(k : Word w)+(d.val : Word w) = (bucket d row t : Word w) := by
    unfold bucket
    rw [ordinal_onRail]
    change _ = (((a-(a/s%g)*s+t.val*s)*k+d.val : ℕ) : Word w)
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_add,Nat.cast_sub erase]
    simp only [Nat.cast_mul]
  have dirRead : m ((dirBase : Word w)+(e : Word w)).val = (d.val : Word w) := by
    rw [address_val _ _ room.dir]
    exact reads.dir
  have cellRead : m ((cellBase : Word w)+(e : Word w)).val = (a : Word w) := by
    rw [address_val _ _ room.cell]
    exact reads.rep
  have powerRead : m ((powerBase : Word w)+(d.val : Word w)).val = (s : Word w) := by
    rw [address_val _ _ room.power]
    exact reads.power
  have finish :
      visit v (cursor e t : Word w) m = ⟨(e : Word w),(t.val : Word w),(bucket d row t : Word w)⟩ := by
    unfold visit
    simp only [gAt,kAt,dirAt,cellAt,powerAt,rail,position,dirRead,cellRead,powerRead,
      divWord_cast a s af sf,digit,key]
  apply wordStep_natStep v C O M B (bucket d row t) e (cursor e t) (decide (h ≠ some t)) m
      rfl rfl rfl rfl (congrArg Visit.rail finish) (congrArg Visit.key finish) _ capFit countFit
      markFit destFit
  rw [finish,touchAt]
  change (m ((touchBase : Word w)+(e : Word w)).val ≠ (t.val : Word w)) ↔ _
  rw [address_val _ _ room.touch, reads.touch, decide_eq_true_eq]
  exact not_congr (tag_eq h t room.radix)

end Hierarchy.GridPassageRAMRow

end OAI
