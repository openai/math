import OAI.Optimization.LinearProgramming.Compression.UniformIndex
import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! ## Dimension-dependent capacity in the address bank of the minor service

The dimension comes from register 22. Six fixed even scratch addresses are enough for
any fixed exponent. All scalar words and the saved odd-address bank survive, except
when the caller explicitly chooses an odd result address. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM GeneratorTable Polynomial

private def capScratch : List ℕ := [24,26,28,30,32,34]

private def seedCapacity (coeff : ℕ) : List AddressSet := [.next 24 22,.fix 28 0,.fix 34 coeff]
private def finishCapacity (rom : ℕ) : List AddressSet := [.read 26 34,.fix 24 rom]

private def capacityPower (coeff : ℕ) : ℕ → Block
  | 0 => addressPlan (seedCapacity coeff)
  | k+1 => .seq (capacityPower coeff k) (.seq (.op (.addrCopy 26 34)) (cellAddress 34 30 32 28 26 24 28))

/-- Builds `coeff*(n+1)^exponent+rom` in `dst`, with `n` initially in address 22.
All immediates are static finite address literals. No scalar is accessed. -/
def monomialCapacity (dst coeff exponent rom : ℕ) : Block :=
  .seq (capacityPower coeff exponent) (.seq (addressPlan (finishCapacity rom))
    (.seq (cellAddress 34 30 32 24 28 28 26) (.op (.addrCopy dst 34))))

private noncomputable def capacityPowerTime (coeff : ℕ) : ℕ → Polynomial ℕ
  | 0 => 3
  | k+1 => capacityPowerTime coeff k + (1+((X+1)*(4*(C coeff*(X+1)^k)+5)+5))

/-- The physical cost is a fixed polynomial in the dimension for every fixed capacity.
The final addition counts up to the constructed monomial; loading the ROM address is one
ordinary immediate-address instruction. -/
noncomputable def monomialCapacityTime (coeff exponent : ℕ) : Polynomial ℕ :=
  capacityPowerTime coeff exponent + (2+((4*(C coeff*(X+1)^exponent)+5)+1))

private structure PowerState {K : Type} (coeff n k : ℕ) (s t : Memory K) : Prop where
  data : t.data=s.data
  value : t.index 34=coeff*(n+1)^k
  factor : t.index 24=n+1
  zero : t.index 28=0
  frame : ∀ p, p∉capScratch → t.index p=s.index p

variable {K : Type}

private theorem power_run [Field K] [LinearOrder K] [IsStrictOrderedRing K] (P : (ℕ→K)→Prop) (s : Memory K) (n coeff k : ℕ)
    (hn : s.index 22=n) (hs : P s.data) : ∃ t,
    Block.Eval (fun m => P m.data) (capacityPower coeff k) s ((capacityPowerTime coeff k).eval n) t ∧
      PowerState coeff n k s t := by
  induction k with
  | zero =>
    let t := applyPlan (seedCapacity coeff) s
    have run := addressPlan_spec P (seedCapacity coeff) s hs
    have seedSize : (seedCapacity coeff).length = 3 := rfl
    rw [seedSize] at run
    refine ⟨t,?_,applyPlan_data _ _,?_,?_,?_,?_⟩
    · change Block.Eval (fun m => P m.data) (addressPlan (seedCapacity coeff)) s
        ((3 : Polynomial ℕ).eval n) (applyPlan (seedCapacity coeff) s)
      simpa only [Polynomial.eval_ofNat] using run
    · simp [t,seedCapacity,applyPlan,AddressSet.apply]
    · simp [t,seedCapacity,applyPlan,AddressSet.apply,hn]
    · simp [t,seedCapacity,applyPlan,AddressSet.apply]
    · intro r hr
      simp [capScratch] at hr
      simp [t,seedCapacity,applyPlan,AddressSet.apply,hr]
  | succ k ih =>
    obtain ⟨u,eu,p⟩ := ih
    let v := u.putIndex 26 (u.index 34)
    have ev : Block.Eval (fun m => P m.data) (.op (.addrCopy 26 34)) u 1 v := Block.Eval.op_addrCopy _ _ _ eu.safe_end eu.safe_end
    obtain ⟨t,et,dt,ft,vt⟩ := cellAddress_spec P v eu.safe_end 34 30 32 28 26 24 28 (by simp [CellScratchOK])
    have v24 : v.index 24=n+1 := by simpa [v] using p.factor
    have v26 : v.index 26=coeff*(n+1)^k := by simpa [v] using p.value
    have v28 : v.index 28=0 := by simpa [v] using p.zero
    simp only [v24,v26,v28,Nat.mul_zero,Nat.zero_add,Nat.add_zero] at et vt
    refine ⟨t,?_,dt.trans p.data,?_,(ft 24 (by decide) (by decide) (by decide)).trans v24,
      (ft 28 (by decide) (by decide) (by decide)).trans v28,?_⟩
    · simpa only [capacityPower,capacityPowerTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
        Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_ofNat] using eu.seq (ev.seq et)
    · rw [vt,pow_succ]; ring
    · intro r hr
      have hh := hr
      simp [capScratch] at hh
      rw [ft r (by omega) (by omega) (by omega)]
      simpa [v,hh] using p.frame r hr

structure MonomialCapacityResult (dst coeff exponent rom n : ℕ) (s t : Memory K) : Prop where
  data : t.data=s.data
  capacity : t.index dst=coeff*(n+1)^exponent+rom
  frame : ∀ p, p≠dst → p∉[24,26,28,30,32,34] → t.index p=s.index p

/-- All saved odd addresses are preserved if the target is even. For an odd target,
that target is the sole writable odd address. -/
theorem MonomialCapacityResult.odd {dst coeff exponent rom n : ℕ} {s t : Memory K}
    (h : MonomialCapacityResult dst coeff exponent rom n s t) (j : ℕ) (hj : 2*j+1≠dst) :
    t.index (2*j+1)=s.index (2*j+1) := h.frame _ hj (by simp; omega)

/-- The scalar predicate can describe the entire entry tape, so every intermediate scalar
is identical to its entry word. The scratch frame is independent of exponent and input. -/
theorem monomialCapacity_spec [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : (ℕ→K)→Prop) (s : Memory K) (dst coeff exponent rom n : ℕ)
    (hn : s.index 22=n) (hs : P s.data) : ∃ t,
    Block.Eval (fun m => P m.data) (monomialCapacity dst coeff exponent rom) s
      ((monomialCapacityTime coeff exponent).eval n) t ∧ MonomialCapacityResult dst coeff exponent rom n s t := by
  obtain ⟨u,eu,p⟩ := power_run P s n coeff exponent hn hs
  let v := applyPlan (finishCapacity rom) u
  have ev : Block.Eval (fun z => P z.data) (addressPlan (finishCapacity rom)) u 2 v :=
    addressPlan_spec _ _ _ eu.safe_end
  obtain ⟨w,ew,dw,fw,vw⟩ := cellAddress_spec P v ev.safe_end 34 30 32 24 28 28 26 (by simp [CellScratchOK])
  have v24 : v.index 24=rom := by simp [v,finishCapacity,applyPlan,AddressSet.apply]
  have v26 : v.index 26=coeff*(n+1)^exponent := by simpa [v,finishCapacity,applyPlan,AddressSet.apply] using p.value
  have v28 : v.index 28=0 := by simpa [v,finishCapacity,applyPlan,AddressSet.apply] using p.zero
  simp only [v24,v26,v28,Nat.zero_mul,Nat.add_zero,Nat.zero_add] at ew vw
  let t := w.putIndex dst (w.index 34)
  have et : Block.Eval (fun m => P m.data) (.op (.addrCopy dst 34)) w 1 t := Block.Eval.op_addrCopy _ _ _ ew.safe_end ew.safe_end
  refine ⟨t,?_,dw.trans ((applyPlan_data _ _).trans p.data),?_,?_⟩
  · simpa only [monomialCapacity,monomialCapacityTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_ofNat] using eu.seq (ev.seq (ew.seq et))
  · simpa [t,Nat.add_comm] using vw
  · intro r hd hr
    have hh := hr
    simp at hh
    rw [show t.index r=w.index r from Memory.putIndex_ne _ hd _,fw r (by omega) (by omega) (by omega)]
    simpa [v,finishCapacity,applyPlan,AddressSet.apply,hh] using p.frame r hr

end Compression
end LinearProgramming
end Optimization
end OAI
