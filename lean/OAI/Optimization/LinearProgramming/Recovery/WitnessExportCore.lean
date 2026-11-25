import OAI.Optimization.LinearProgramming.Recovery.BankRead
import OAI.Optimization.LinearProgramming.RAM.CallableScopedAccess

/-! Export the successful rectangular solve's contiguous vector from the native even
bank to a caller-selected data interval in the odd bank. The copy uses address
registers 180–183 and scalar scratch register 4. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessExport

open RAM RAM.Block RAM.Callable

/-- Register 63 points to the augmented coefficient vector. The published solution
occupies positions one through the requested dimension. -/
private def setupOps : List Instr :=
  [.incr 180 180, .addrCopy 181 210, .addrCopy 182 211]

def program : Fragment :=
  (Fragment.ofBlock (BankRead.receiveIndex 63 180)).seq
    ((Odd.leaf (.straight setupOps)).seq (Fragment.ofBlock BankRead.copyWindow))

instance program_fixedAccess : Fragment.FixedAccess program := by
  unfold program Odd.leaf
  infer_instance

def time (d : ℕ) : ℕ := 21*d+18

/-- The field data copied by the program, including all caller fields outside the
destination and every caller address register above the working area. -/
theorem program_run_values {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (native caller : Memory K)
    (hn : native.AllData P) (hc : caller.AllData P) (d dst : ℕ) (w : Fin d → K)
    (hdst : caller.index 210 = dst) (hd : caller.index 211 = d) (hbase : 5 ≤ dst)
    (values : ∀ j : Fin d, native.data (native.index 63+j.succ.val) = w j) :
    ∃ t, program.Run P (Odd.memory native caller) (time d) (Odd.memory native t) ∧
      t.AllData P ∧ (∀ j : Fin d, t.data (dst+j.val) = w j) ∧
      (∀ p, 200 ≤ p → t.index p = caller.index p) ∧
      (∀ p, 5 ≤ p → (p < dst ∨ dst+d ≤ p) → t.data p = caller.data p) := by
  let a := caller.putIndex 180 (native.index 63)
  let b := a.putIndex 180 (a.index 180+1)
  let c := b.putIndex 181 (b.index 210)
  let z := c.putIndex 182 (c.index 211)
  have ha : a.AllData P := hc
  have hb : b.AllData P := hc
  have hC : c.AllData P := hc
  have hz : z.AllData P := hc
  have recv : (Fragment.ofBlock (BankRead.receiveIndex 63 180)).Run P
      (Odd.memory native caller) 1 (Odd.memory native a) :=
    Fragment.Run.ofBlock (BankRead.receiveIndex_eval P native caller hn hc 63 180)
  have setup : Block.Eval (Memory.AllData P) (.straight setupOps) a 3 z :=
    (Block.Eval.op_incr (safe := Memory.AllData P) a 180 180 ha hb).seq
      ((Block.Eval.op_addrCopy (safe := Memory.AllData P) b 181 210 hb hC).seq
        ((Block.Eval.op_addrCopy (safe := Memory.AllData P) c 182 211 hC hz).seq (.skip hz)))
  have lifted := Odd.leaf_run P native hn setup
  have src : z.index 180 = native.index 63 + 1 := by simp [z,c,b,a]
  have dest : z.index 181 = dst := by simp [z,c,b,a,hdst]
  have len : z.index 182 = d := by simp [z,c,b,a,hd]
  obtain ⟨t,k,cost,copy,word,frame,_,_,_,header⟩ :=
    BankRead.copyWindow_eval P native z hn hz (native.index 63+1) dst d src dest len hbase
  refine ⟨t,(recv.seq (lifted.seq (Fragment.Run.ofBlock copy))).mono ?_,?_,?_,?_,?_⟩
  · unfold time
    omega
  · intro p
    simpa using copy.safe_end (Odd.slot p)
  · intro j
    calc
      t.data (dst+j.val) = native.data (native.index 63+1+j.val) := word j.val j.isLt
      _ = native.data (native.index 63+j.succ.val) := by
        congr 1
        change native.index 63 + 1 + j.val = native.index 63 + (j.val+1)
        omega
      _ = w j := values j
  · intro p hp
    have a180 : p ≠ 180 := by omega
    have a181 : p ≠ 181 := by omega
    have a182 : p ≠ 182 := by omega
    have a183 : p ≠ 183 := by omega
    rw [header p a180 a181 a183]
    simp only [z,c,b,a,Memory.putIndex_ne _ a180,Memory.putIndex_ne _ a181,Memory.putIndex_ne _ a182]
  · intro p hp outside
    exact frame p (by omega) outside

end WitnessExport
end Recovery
end LinearProgramming
end Optimization
end OAI
