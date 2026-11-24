import OAI.Computability.VPVNP.RAMTapePublicExprComposition
import OAI.Computability.VPVNP.RAMTapePublicExprLog

/-! # A fixed finite stack program for every live public operand expression

The syntax fixes the instruction table and the number of temporary registers.
Word width and operand values come from the parsed geometry at execution time.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicExprMachine

open BurstRAM PrivateRAM LiveProgram

/-- Number of extra registers required above the result slot to evaluate an expression
recursively. -/
def extra : PublicExpr → ℕ
  | .add a b | .sub a b | .mul a b => max (extra a) (extra b + 1)
  | .divConst a _ | .pow2 a => max (extra a) 1
  | .log2 a | .clog2 a => extra a
  | _ => 0

/-- Number of syntax-tree nodes, counting geometry parameters and literals as leaves. -/
def nodes : PublicExpr → ℕ
  | .add a b | .sub a b | .mul a b => nodes a + nodes b + 1
  | .divConst a _ | .pow2 a | .log2 a | .clog2 a => nodes a + 1
  | _ => 1

/-- Compile the expression into a fixed register program that writes at its base and stages a
binary right operand one register higher. -/
def compile (r base : ℕ) : PublicExpr → FiniteRoutine (BankPort r)
  | .lit n => ISA.loadLiteral n (addr r base)
  | .n => load (addr r base) 0
  | .d => load (addr r base) 1
  | .H => load (addr r base) 2
  | .w => load (addr r base) 3
  | .add a b => combine .add base (compile r base a) (compile r (base+1) b)
  | .sub a b => combine .sub base (compile r base a) (compile r (base+1) b)
  | .mul a b => combine .mul base (compile r base a) (compile r (base+1) b)
  | .divConst a n => constant (.divConst n) base (compile r base a)
  | .pow2 a => constant .pow2 base (compile r base a)
  | .log2 a => (compile r base a).followedBy (PublicExprLog.code false (addr r base))
  | .clog2 a => (compile r base a).followedBy (PublicExprLog.code true (addr r base))

/-- Quadratic step allowance for a single compiled expression node at the given word width. -/
def nodeCost (w : ℕ) := 150*(w+1)^2

private theorem logarithm_computes {g : Geometry} {r base x t : ℕ} (ceil : Bool)
    {a : FiniteRoutine (BankPort r)} (hb : base ≤ r) (hx : x < 2^g.w)
    (ha : Computes g r base x t a) :
    Computes g r base (if ceil then Nat.clog 2 x else Nat.log 2 x) (t+nodeCost g.w)
      (a.followedBy (PublicExprLog.code ceil (addr r base))) := by
  intro p rs log
  obtain ⟨u,hu,z,first,hz,keep⟩ := ha p rs log
  obtain ⟨v,hv,hr⟩ := PublicExprLog.runs ceil (addr r base) (geometryWords g) p z log
  have val : (z (addr r base)).val = x := hz ▸ packed_val hx
  rw [val] at hr
  refine ⟨_, Nat.add_le_add hu (hv.trans ?_), _, first.followedBy hr, Function.update_self .., ?_⟩
  · exact Nat.mul_le_mul_right _ (by decide : 12 ≤ 150)
  · intro i hi
    rw [Function.update_of_ne (by intro he; rw [he, addr_val hb] at hi; omega), keep i hi]

private theorem fits_value {g : Geometry} {e : PublicExpr} {n : ℕ} (h : e.Fits g n) : e.eval g < n := by
  cases e <;> exact h.1

theorem compile_computes (g : Geometry) (r base : ℕ) (e : PublicExpr)
    (hr : base + extra e ≤ r) (hf : e.Fits g (2^g.w)) :
    Computes g r base (e.eval g) (nodes e * nodeCost g.w) (compile r base e) := by
  have hlinear : 8*g.w+3 ≤ nodeCost g.w := by unfold nodeCost; nlinarith [Nat.zero_le (g.w*g.w)]
  induction e generalizing base with
  | lit n =>
    exact (literal_computes g base n (by simpa [extra] using hr)).mono (by simpa [nodes] using hlinear)
  | n =>
    exact (load_computes g base 0 (by simpa [extra] using hr)).mono (by simpa [nodes] using hlinear)
  | d =>
    exact (load_computes g base 1 (by simpa [extra] using hr)).mono (by simpa [nodes] using hlinear)
  | H =>
    exact (load_computes g base 2 (by simpa [extra] using hr)).mono (by simpa [nodes] using hlinear)
  | w =>
    exact (load_computes g base 3 (by simpa [extra] using hr)).mono (by simpa [nodes] using hlinear)
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [extra] at hr
    obtain ⟨_, hfa, hfb⟩ := hf
    simp only [compile, nodes, Nat.add_mul, Nat.one_mul]
    apply combine_computes g _ (by omega) (fits_value hfa) (fits_value hfb) (ha base (by omega) hfa) (hb (base+1) (by omega) hfb)
  | divConst a n ha =>
    simp only [extra] at hr
    obtain ⟨hout, hfa, hlit⟩ := hf
    simp only [compile, nodes, Nat.add_mul, Nat.one_mul]
    exact constant_computes g (.divConst n) (by omega) (fits_value hfa) hlit hout (ha base (by omega) hfa)
  | pow2 a ha =>
    simp only [extra] at hr
    obtain ⟨hout, hfa⟩ := hf
    simp only [compile, nodes, Nat.add_mul, Nat.one_mul]
    have hunit : 1 < 2^g.w := (Nat.one_le_two_pow (n := a.eval g)).trans_lt hout
    exact constant_computes g .pow2 (by omega) (fits_value hfa) hunit hout (ha base (by omega) hfa)
  | log2 a ha =>
    obtain ⟨_, hfa⟩ := hf
    simp only [compile, nodes, Nat.add_mul, Nat.one_mul]
    exact logarithm_computes false (by simp only [extra] at hr; omega) (fits_value hfa) (ha base hr hfa)
  | clog2 a ha =>
    obtain ⟨_, hfa⟩ := hf
    simp only [compile, nodes, Nat.add_mul, Nat.one_mul]
    exact logarithm_computes true (by simp only [extra] at hr; omega) (fits_value hfa) (ha base hr hfa)

end RAMTape.PublicExprMachine

end VPVNP
end Computability
end OAI
