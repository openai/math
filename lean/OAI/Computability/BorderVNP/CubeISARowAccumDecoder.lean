import OAI.Computability.BorderVNP.CubeISARowAccum
import OAI.Computability.BorderVNP.DiagonalTallyPacketBank

/-! # Native radix decoding of the physical selector word

The selector numbering puts its copy number above all the directed-edge
digits. Starting with the whole encoded selector, one quotient and remainder
per slot recover the canonical edge ordinal while leaving the copy number
in the final quotient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RowAccum

open RoutingISA VPVNP.BurstRAM Physical Tally

/-- The edge ordinal in the physical packet bank gives the direction as its low digit. -/
theorem edgeOrder_mod {a : ℕ} (e : Edge a) : (edgeOrder a e).val % a = e.2.val := by
  rw [edgeOrder_val,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt e.2.isLt]

/-- Every low-order radix digit of the full canonical selector is its indicated edge. -/
theorem selectorOrder_digit {n h K : ℕ} (u : Selector n K h) (i : Fin h) :
    (selectorOrder n K h u).val / Fintype.card (Edge (n+1))^i.val % Fintype.card (Edge (n+1)) =
      (edgeOrder (n+1) (u.2 i)).val := by
  let E := Fintype.card (Edge (n+1))
  let f : Fin h → Fin E := fun k => edgeOrder (n+1) (u.2 k)
  have hE : 0 < E := Fintype.card_pos
  have digit : (finFunctionFinEquiv f).val / E^i.val % E = (f i).val :=
    congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply f) i)
  change ((finFunctionFinEquiv f).val + E^h*u.1.val) / E^i.val % E = (f i).val
  have exp : h = i.val+(1+(h-i.val-1)) := by have := i.isLt; omega
  have factor : E^h*u.1.val = E^i.val*(E*(E^(h-i.val-1)*u.1.val)) := by
    have he := congrArg (E ^ ·) exp
    rw [pow_add, pow_add, pow_one] at he
    rw [he]
    ac_rfl
  rw [factor,Nat.add_mul_div_left _ _ (pow_pos hE _),Nat.add_mul_mod_self_left,digit]

/-- Decoded digit array after the first `i` stores. -/
def digitImage (old : ℕ → ℕ) (dst radix code i a : ℕ) : ℕ :=
  if dst ≤ a ∧ a < dst+i then code / radix^(a-dst) % radix else old a

private theorem digitImage_succ (old : ℕ → ℕ) (dst radix code i : ℕ) :
    Function.update (digitImage old dst radix code i) (dst+i) (code / radix^i % radix) =
      digitImage old dst radix code (i+1) := by
  funext a
  by_cases eq : a = dst+i
  · subst a
    simp [digitImage]
  · rw [Function.update_of_ne eq]
    have same : (dst ≤ a ∧ a < dst+i) ↔ (dst ≤ a ∧ a < dst+(i+1)) := by omega
    simp only [digitImage,same]

/-- Fixed quotient, remainder and store sequence for the next edge ordinal. -/
def decodeStep : RoutingISA.Code := .block [
  .binary .mod 52 51 44, .binary .add 53 47 50, .store 53 52,
  .binary .div 51 51 44, .binary .add 50 50 55]

/-- Decode the word in register 43 in radix 44 into `r48` words at address `r47`. -/
def decodeLoop : RoutingISA.Code := .seq (.block [.constant 50 0,.constant 55 1,.copy 51 43])
  (.whileLt 50 48 decodeStep)

private def decodeReady (dst radix count : ℕ) (z : NatState) : Prop :=
  z.reg 44 = radix ∧ z.reg 47 = dst ∧ z.reg 48 = count

private theorem decodeReady_keep {dst radix count : ℕ} {z : NatState} {c : RoutingISA.Code}
    (hz : decodeReady dst radix count z) (hc : c.protects 50 = true) (env : Arg → ℕ) :
    decodeReady dst radix count (c.fixedEval env z) :=
  ⟨(c.fixedEval_protected env z hc 44 (by decide)).trans hz.1,
    (c.fixedEval_protected env z hc 47 (by decide)).trans hz.2.1,
    (c.fixedEval_protected env z hc 48 (by decide)).trans hz.2.2⟩

/-- Execute the actual selector decoder. The complete selector word is preserved in
register 43 and the scratch array contains all of its indicated low-order edge ordinals. -/
theorem decodeLoop_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (dst radix count code : ℕ)
    (rc : (r 43).val = code) (rd : (r 44).val = radix)
    (rb : (r 47).val = dst) (rh : (r 48).val = count)
    (pos : 0 < radix) (room : dst+count ≤ 2^w) :
    BoundedRun pub macros decodeLoop r m (6*count+4) (fun z =>
      z.mem = digitImage (readings m) dst radix code count ∧
      ∀ k : Reg, k.val < 50 → z.reg k = (r k).val) := by
  let image := digitImage (readings m) dst radix code
  let P i z := decodeReady dst radix count z ∧ z.reg 50 = i ∧ z.reg 55 = 1 ∧
    z.reg 51 = code / radix^i ∧ z.mem = image i ∧ ∀ k : Reg, k.val < 50 → z.reg k = (r k).val
  have oneFit : 1 < 2^w := (Nat.succ_le_of_lt pos).trans_lt (rd ▸ (r 44).isLt)
  have regs i z (hz : P i z) : z.reg 50 = i ∧ z.reg 48 = count := ⟨hz.2.1,hz.1.2.2⟩
  have step (i : ℕ) (hi : i < count) (t : Bank w) (mt : Memory w) (hp : P i (.ofWords t mt)) :
      BoundedRun pub macros decodeStep t mt 5 (P (i+1)) := by
    let z := NatState.ofWords t mt
    have hz : decodeReady dst radix count z := hp.1
    obtain ⟨d,b,_⟩ := hz
    have idx : z.reg 50 = i := hp.2.1
    have one : z.reg 55 = 1 := hp.2.2.1
    have q : z.reg 51 = code / radix^i := hp.2.2.2.1
    have mem : z.mem = image i := hp.2.2.2.2.1
    have rfit : dst+i < 2^w := by omega
    have inc : i+1 < 2^w := (Nat.succ_le_of_lt hi).trans_lt (rh ▸ (r 48).isLt)
    have safe : decodeStep.fixedSafe w (readings pub) z := by
      simp (config := {decide := true}) [decodeStep,RoutingISA.Code.block,RoutingISA.Code.fixedSafe,
        RoutingISA.Code.fixedEval,RoutingISA.Code.safeReadOnly,RoutingISA.Code.evalNat,addressOpFits,
        d,b,idx,one,pos,rfit,inc]
    apply (decodeStep.runFixed pub macros t mt safe).mono (by decide)
    rintro y rfl
    change P (i+1) (decodeStep.fixedEval (readings pub) z)
    refine ⟨decodeReady_keep hp.1 (by decide) _,?_,?_,?_,?_,?_⟩
    · simp (config := {decide := true}) [decodeStep,RoutingISA.Code.block,RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,addressOp,idx,one]
    · simp (config := {decide := true}) [decodeStep,RoutingISA.Code.block,RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,one]
    · simp (config := {decide := true}) [decodeStep,RoutingISA.Code.block,RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,addressOp,q,d,Nat.div_div_eq_div_mul,pow_succ]
    · simp (config := {decide := true}) [decodeStep,RoutingISA.Code.block,RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,addressOp,idx,q,d,b,mem,image,digitImage_succ]
    · intro k hk
      exact (decodeStep.fixedEval_protected _ z (lo := 50) (by decide) k hk).trans (hp.2.2.2.2.2 k hk)
  let init := RoutingISA.Code.block [.constant 50 0,.constant 55 1,.copy 51 43]
  have ready : decodeReady dst radix count (.ofWords r m) := ⟨rd,rb,rh⟩
  have run := (init.runFixed pub macros r m (by
    simp [init,RoutingISA.Code.block,RoutingISA.Code.fixedSafe,RoutingISA.Code.safeReadOnly,oneFit])).seq
    (b := .whileLt 50 48 decodeStep) (t := (count-0)*(5+1)+1) (Q := P count)
    (fun t mt eq => run_counted_loop pub macros 50 48 decodeStep count 5 P regs step 0 (by omega) t mt (by
      rw [eq]
      refine ⟨decodeReady_keep ready (by decide) _,?_,?_,?_,?_,?_⟩
      · simp (config := {decide := true}) [init,RoutingISA.Code.block,RoutingISA.Code.fixedEval,RoutingISA.Code.evalNat]
      · simp (config := {decide := true}) [init,RoutingISA.Code.block,RoutingISA.Code.fixedEval,RoutingISA.Code.evalNat]
      · simp (config := {decide := true}) [init,RoutingISA.Code.block,RoutingISA.Code.fixedEval,RoutingISA.Code.evalNat,
          NatState.ofWords,readings,rc]
      · funext a
        simp [init,RoutingISA.Code.block,RoutingISA.Code.fixedEval,NatState.ofWords,image,digitImage]
      · intro k hk
        exact init.fixedEval_protected _ _ (lo := 50) (by decide) k hk))
  exact run.mono (by change 3+(count-0)*(5+1)+1 ≤ _; omega) fun _ hz => hz.2.2.2.2

end Cube.RowAccum

end BorderVNP
end Computability
end OAI
