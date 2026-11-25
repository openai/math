import OAI.Optimization.LinearProgramming.RAM.Code

/-! Registers with even addresses simulate the callee. Odd addresses preserve the
caller's original data and saved results. Scaling the address *values* as well as their
locations lets a simulated indirect memory access use one RAM instruction. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

variable {K : Type*}

open RAM

def pack (v frame : Memory K) : Memory K where
  data i := if i % 2 = 0 then v.data (i/2) else frame.data (i/2)
  index i := if i % 2 = 0 then 2 * v.index (i/2) else frame.index (i/2)

@[simp] theorem data_even (v f : Memory K) (i : Nat) : (pack v f).data (2*i) = v.data i := by
  simp [pack]

@[simp] theorem index_even (v f : Memory K) (i : Nat) : (pack v f).index (2*i) = 2*v.index i := by
  simp [pack]

@[simp] theorem data_odd (v f : Memory K) (i : Nat) : (pack v f).data (2*i+1) = f.data i := by
  simp [pack, show (2*i+1)/2 = i by omega]

@[simp] theorem index_odd (v f : Memory K) (i : Nat) : (pack v f).index (2*i+1) = f.index i := by
  simp [pack, show (2*i+1)/2 = i by omega]

private theorem mem_ext {m n : Memory K} (hd : ∀ j, m.data j = n.data j)
    (hi : ∀ j, m.index j = n.index j) : m = n := by
  cases m; cases n
  congr <;> funext j
  · exact hd j
  · exact hi j

/-- Split an arbitrary register address into an even or odd case. -/
private theorem even_odd_elim (P : Nat → Prop) (he : ∀ j, P (2*j)) (ho : ∀ j, P (2*j+1))
    (i : Nat) : P i := by
  by_cases h : i%2=0
  · exact (show 2*(i/2)=i by omega) ▸ he (i/2)
  · exact (show 2*(i/2)+1=i by omega) ▸ ho (i/2)

@[simp] theorem pack_write_data (v f : Memory K) (i : Nat) (x : K) :
    (pack v f).putData (2*i) x = pack (v.putData i x) f := by
  apply mem_ext
  · apply even_odd_elim
    · intro j
      by_cases h : j=i
      · subst j; simp [Memory.putData]
      · have h₂ : 2*j ≠ 2*i := by omega
        simp [Memory.putData, Function.update_of_ne, h, h₂]
    · intro j
      have h : 2*j+1 ≠ 2*i := by omega
      simp [Memory.putData, Function.update_of_ne h]
  · exact even_odd_elim _ (fun j => by simp [Memory.putData]) (fun j => by simp [Memory.putData])

@[simp] theorem pack_write_index (v f : Memory K) (i n : Nat) :
    (pack v f).putIndex (2*i) (2*n) = pack (v.putIndex i n) f := by
  apply mem_ext
  · exact even_odd_elim _ (fun j => by simp [Memory.putIndex]) (fun j => by simp [Memory.putIndex])
  · apply even_odd_elim
    · intro j
      by_cases h : j=i
      · subst j; simp [Memory.putIndex]
      · have h₂ : 2*j ≠ 2*i := by omega
        simp [Memory.putIndex, Function.update_of_ne, h, h₂]
    · intro j
      have h : 2*j+1 ≠ 2*i := by omega
      simp [Memory.putIndex, Function.update_of_ne h]

theorem pack_scalar_bound (v f : Memory ℚ) (B : Nat)
    (hv : ∀ i, ratBits (v.data i) ≤ B) (hf : ∀ i, ratBits (f.data i) ≤ B) :
    ∀ i, ratBits ((pack v f).data i) ≤ B :=
  even_odd_elim _ (fun j => by simpa using hv j) (fun j => by simpa using hf j)

/-- Physical fall-through width for a single simulated instruction. -/
def width : Instr → Nat
  | .incr .. | .decr .. => 2
  | _ => 1

/-- Return instructions jump to a caller-chosen continuation for their literal tag. -/
def emit (ret addr : Nat → Nat) : Instr → Program
  | .const d q => [.const (2*d) q]
  | .copy d a => [.copy (2*d) (2*a)]
  | .add d a b => [.add (2*d) (2*a) (2*b)]
  | .sub d a b => [.sub (2*d) (2*a) (2*b)]
  | .mul d a b => [.mul (2*d) (2*a) (2*b)]
  | .div d a b => [.div (2*d) (2*a) (2*b)]
  | .load d a => [.load (2*d) (2*a)]
  | .store a d => [.store (2*a) (2*d)]
  | .addrConst d n => [.addrConst (2*d) (2*n)]
  | .addrCopy d a => [.addrCopy (2*d) (2*a)]
  | .incr d a => [.incr (2*d) (2*a), .incr (2*d) (2*d)]
  | .decr d a => [.decr (2*d) (2*a), .decr (2*d) (2*d)]
  | .addrLoad d a => [.addrLoad (2*d) (2*a)]
  | .addrStore a d => [.addrStore (2*a) (2*d)]
  | .branchLT a b y n => [.branchLT (2*a) (2*b) (addr y) (addr n)]
  | .branchAddrLT a b y n => [.branchAddrLT (2*a) (2*b) (addr y) (addr n)]
  | .jump j => [.jump (addr j)]
  | .halt tag => [.jump (ret tag)]

@[simp] theorem emit_length (ret addr : Nat → Nat) (i : Instr) :
    (emit ret addr i).length = width i := by cases i <;> rfl

theorem width_le_two (i : Instr) : width i ≤ 2 := by cases i <;> simp [width]

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
