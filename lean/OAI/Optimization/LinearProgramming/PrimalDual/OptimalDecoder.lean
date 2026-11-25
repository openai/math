import OAI.Optimization.LinearProgramming.PrimalDual.PassesRAM
import OAI.Optimization.LinearProgramming.PrimalDual.Raw

/-! Physical output decoder for infeasible and finite-optimum branches. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape Matrix

/-- The caller supplies length in address register 6 and the two last addresses
in registers 7 and 8. This branch returns tag 0 after the reverse copy. -/
def infeasibleDecoder : Block := copyFromRegs true 7 8 6

theorem infeasibleDecoder_correct {m d H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) (s : Memory ℚ) (base : Nat) (hs : Good (fun q => ratBits q ≤ H) s)
    (hbase : m ≤ base) (hpos : 0 < base) (h6 : s.index 6 = m)
    (h7 : s.index 7 = base+m-1) (h8 : s.index 8 = m-1)
    (y : Fin m → ℚ) (hy : Holds s base y) (cert : Certificate A b y) :
    ∃ t, Eval (Good (fun q => ratBits q ≤ H)) infeasibleDecoder s (7*m+5) t ∧
      OptimizationOutput A b c {t.atPC 0 with output := some 0} := by
  obtain ⟨t,run,out,_,_⟩ := copyFromRegs_correct true m base 0 7 8 6 s hs (by decide) (by decide) (by decide)
    h7 (by simpa [startPointer] using h8) h6 (.inr (by omega)) hpos
  refine ⟨t,run,Or.inl ⟨rfl,?_⟩⟩
  have e : readVector ({t.atPC 0 with output := some 0}) 0 m = y := by
    funext i; simpa [readVector,Memory.atPC] using (out i.val i.isLt).trans (hy i)
  rwa [e]

/-- The joint primal and dual vectors are contiguous. The dot pass computes the
missing scalar objective, the store writes it immediately after the vectors,
and the final reverse copy serializes the whole answer to address zero. -/
def optimumDecoder : Block :=
  .seq (OutputPass.scanFromRegs .dot 9 8 9 6) (.seq (.op (.store 10 3)) (copyFromRegs true 10 11 7))

/-- Address registers for a finite optimum. Reg 8 is the base of the packed
primal/dual vector and reg 9 is the objective coefficient base. -/
structure OptimumReady {m d : Nat} (s : Memory ℚ) (z obj : Nat) : Prop where
  dimension : s.index 6 = d
  length : s.index 7 = d+m+1
  joint : s.index 8 = z
  objective : s.index 9 = obj
  valueSlot : s.index 10 = z+d+m
  last : s.index 11 = d+m
  jointHigh : 4 ≤ z
  objHigh : 4 ≤ obj
  disjoint : d+m+1 ≤ z

/-- The actual primitive machine instructions on tag 1 recover the optimum
and charge the full integer arithmetic cost and intermediate rational sizes. -/
theorem optimumDecoder_correct {m d H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) (s : Memory ℚ) (z obj : Nat) (abi : OptimumReady (m := m) (d := d) s z obj)
    (hs : Good (fun q => ratBits q ≤ H) s) (joint : State ℚ)
    (hj : Feasible (finJointMatrix A b c) (finJointRhs b c) (readVector joint 0 (d+m)))
    (hx : Holds s z (readVector joint 0 d)) (hy : Holds s (z+d) (readVector joint d m))
    (hc : Holds s obj c) :
    ∃ t, Eval (Good (fun q => ratBits q ≤ decoderLimit d H)) optimumDecoder s (17*d+7*m+20) t ∧
      OptimizationOutput A b c {t.atPC 0 with output := some 1} := by
  let x := readVector joint 0 d
  let y := readVector joint d m
  obtain ⟨hpr,hpos,hdc,hval,hmax,_⟩ := raw_joint_optimum A b c joint hj
  obtain ⟨hH,h0,_,hSum,_,hProd,_,_⟩ := decoderLimit_bounds d H
  have safe : Good (fun q => ratBits q ≤ decoderLimit d H) s := fun i => (hs i).trans hH
  have cx (i : Fin d) : ratBits (c i) ≤ H := (hc i) ▸ hs (obj+i.val)
  have xx (i : Fin d) : ratBits (x i) ≤ H := (congrArg ratBits (hx i)).symm.trans_le (hs _)
  obtain ⟨s1,e1,acc,frame,idx⟩ := dotPass c x obj z 9 8 6 s safe (by decide) (by decide) (by decide)
    abi.objective abi.joint abi.dimension abi.objHigh abi.jointHigh hc hx cx xx hProd hSum h0
  let s2 := s1.putData (s1.index 10) (s1.data 3)
  have e2 : Eval (Good (fun q => ratBits q ≤ decoderLimit d H)) (.op (.store 10 3)) s1 1 s2 :=
    Eval.op_store s1 10 3 e1.safe_end (safe_data_write _ e1.safe_end _ _ (e1.safe_end 3))
  have p10 : s1.index 10 = z+d+m := (idx 10 (by decide)).trans abi.valueSlot
  have rsrc : s2.index 10 = startPointer true z (d+m+1) := by simp [s2,p10,startPointer]; omega
  have rdst : s2.index 11 = startPointer true 0 (d+m+1) := by
    simpa [s2,startPointer] using (idx 11 (by decide)).trans abi.last
  obtain ⟨t,e3,out,_,_⟩ := copyFromRegs_correct true (d+m+1) z 0 10 11 7 s2 e2.safe_end
    (by decide) (by decide) (by decide) rsrc rdst ((idx 7 (by decide)).trans abi.length)
    (.inr (by simpa using abi.disjoint)) (show 0 < z from lt_of_lt_of_le (by decide : 0 < 4) abi.jointHigh)
  have readX (i : Fin d) : t.data i.val = x i := by
    have o := out i.val (by omega)
    simp only [Nat.zero_add] at o; rw [o]
    change (s1.putData (s1.index 10) _).data _ = _
    rw [Memory.putData_ne _ (by rw [p10]; omega),frame _ (by have := abi.jointHigh; omega),hx i]
  have readY (i : Fin m) : t.data (d+i.val) = y i := by
    have o := out (d+i.val) (by omega)
    simp only [Nat.zero_add] at o; rw [o]
    change (s1.putData (s1.index 10) _).data _ = _
    rw [Memory.putData_ne _ (by rw [p10]; omega),frame _ (by have := abi.jointHigh; omega)]
    simpa only [Nat.add_assoc] using hy i
  have readVal : t.data (d+m) = c ⬝ᵥ x := by
    have o := out (d+m) (by omega)
    simp only [Nat.zero_add] at o; rw [o]
    change (s1.putData (s1.index 10) _).data _ = _
    rw [p10,Nat.add_assoc,Memory.putData_same,acc]
  have eX : readVector ({t.atPC 0 with output := some 1}) 0 d = x := by
    funext i; simpa [readVector,Memory.atPC] using readX i
  have eY : readVector ({t.atPC 0 with output := some 1}) d m = y := by funext i; exact readY i
  refine ⟨t,?_,Or.inr (Or.inl ⟨rfl,?_⟩)⟩
  · have E := e1.seq (e2.seq e3)
    convert E using 1 <;> first | rfl | omega
  · change Feasible A b _ ∧ 0 ≤ _ ∧ Aᵀ *ᵥ _ = c ∧ c ⬝ᵥ _ = t.data (d+m) ∧
      b ⬝ᵥ _ = t.data (d+m) ∧ ∀ z', Feasible A b z' → c ⬝ᵥ z' ≤ t.data (d+m)
    rw [eX,eY,readVal]
    exact ⟨hpr,hpos,hdc,rfl,hval,hmax⟩

end PrimalDual
end LinearProgramming
end Optimization
end OAI
