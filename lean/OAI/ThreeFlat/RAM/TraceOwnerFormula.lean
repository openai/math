import OAI.ThreeFlat.Diagonal.TraceSourceDigits
import OAI.ThreeFlat.RAM.PhysicalPinsFit

namespace OAI
/-! # Fixed native word formulas for source ownership and padded hidden slots -/

namespace ThreeFlat.RAM.TraceOwnerFormula

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing BigOperators

abbrev Form := Formula 18
private abbrev R (i : Fin 18) : Form := .reg i

/-- The first two scalars are operands. The remaining words are fixed shape
data, including the lengths of the regions in the absolute address space. -/
def vars (s : Shape) (word x y : ℕ) : Fin 18 → ℕ :=
  ![x, y, s.header, word, s.cpu, s.rows, s.track, s.edge, s.copy, s.gates,
    s.header*word, s.ticks*s.cpu, s.layers*(s.rows*s.track), (s.rows-1)*s.edge,
    s.rows*s.copy, s.rows*s.track, s.layers*s.track, 2*s.cpu]

def branch (x len : Form) (yes no : Form → Form) : Form :=
  lt x len (yes x) (no (sub x len))

theorem branch_natural (x len : Form) (yes no : Form → Form) (W : ℕ)
    (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 18 → ℕ) :
    (branch x len yes no).natural W data mem vs =
      if x.natural W data mem vs < len.natural W data mem vs then (yes x).natural W data mem vs
      else (no (sub x len)).natural W data mem vs := by
  by_cases h : x.natural W data mem vs < len.natural W data mem vs <;>
    simp [branch,Formula.natural,natTest,h]

private def hidden (row : Bool) (x : Form) : Form :=
  branch x (R 11)
    (fun i =>
      let clock := add (R 2) (div i (R 4))
      if row then div clock (L 2) else add (mul (rem clock (L 2)) (R 4)) (rem i (R 4)))
    (fun x => branch x (R 12)
      (fun i => if row then rem (div i (R 6)) (R 5)
        else add (add (R 17) (mul (div i (R 15)) (R 6))) (rem i (R 6)))
      (fun x => branch x (R 13)
        (fun i => if row then div i (R 7) else add (R 17) (add (R 16) (rem i (R 7))))
        (fun x => branch x (R 14)
          (fun i => if row then div i (R 8) else add (R 17) (add (R 16) (add (R 7) (rem i (R 8)))))
          (fun i => if row then div i (R 9) else add (R 17) (add (R 16) (add (R 7) (add (R 8) (rem i (R 9)))))))))

/-- Scalar output on the external absolute address or a hidden ordinal. -/
inductive Output where | owner | row | slot | reverse
  deriving DecidableEq

def formula : Output → Form
  | .owner => branch (R 0) (L 2) (fun _ => R 1)
      (fun u => branch u (R 10) (fun j => div (div j (R 3)) (L 2)) (hidden true))
  | .row => hidden true (R 0)
  | .slot => hidden false (R 0)
  | .reverse =>
    branch (R 1) (R 17)
      (fun j => add (mul (sub (add (mul (L 2) (R 0)) (div j (R 4))) (R 2)) (R 4)) (rem j (R 4)))
      (fun a => add (R 11) (branch a (R 16)
        (fun j => add (mul (div j (R 6)) (R 15)) (add (mul (R 0) (R 6)) (rem j (R 6))))
        (fun b => add (R 12) (branch b (R 7) (fun j => add (mul (R 0) (R 7)) j)
          (fun c => add (R 13) (branch c (R 8) (fun j => add (mul (R 0) (R 8)) j)
            (fun j => add (R 14) (add (mul (R 0) (R 9)) j))))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem small (q : Output) : Small (formula q) := by
  cases q <;> constructor <;> cbv

theorem fits (q : Output) {b W : ℕ} (data : Param → ℕ) (mem : ℕ → ℕ) (v : Fin 18 → ℕ)
    (margin : 5*b+128 ≤ W) (hd : ∀ i,data i<2^b) (hm : ∀ i,mem i<2^W) (hv : ∀ i,v i<2^b) :
    (formula q).Fits W data mem v := (small q).fits data mem v margin hd hm hv

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem outBound (q : Output) :
    (Estimate.analyze (formula q)).out.shape≤5 ∧ (Estimate.analyze (formula q)).out.word=0 ∧
      (Estimate.analyze (formula q)).out.extra≤128 := by
  cases q <;> decide

theorem output_lt (q : Output) {b W : ℕ} (v : Fin 18 → ℕ)
    (margin : 5*b+128 ≤ W) (hv : ∀ i, v i<2^b) :
    (formula q).natural W (fun _ => 0) (fun _ => 0) v < 2^(5*b+128) := by
  obtain ⟨ho,hw,he⟩ := outBound q
  have hn : (Estimate.analyze (formula q)).needed.total b W ≤ W := by
    simp only [Estimate.Bits.total,(small q).word,Nat.zero_mul,Nat.add_zero]
    exact (Nat.add_le_add (Nat.mul_le_mul_right b (small q).shape) (small q).extra).trans margin
  have h := (Estimate.sound (formula q) (fun _ => 0) (fun _ => 0) v
    (fun _ => Nat.two_pow_pos _) (fun _ => Nat.two_pow_pos _) hv (small q).allowed hn).2
  apply h.trans_le
  apply Nat.pow_le_pow_right (by decide)
  simp only [Estimate.Bits.total,hw,Nat.zero_mul,Nat.add_zero]
  exact Nat.add_le_add (Nat.mul_le_mul_right b ho) he

/-- Native code, with caller-selected public-word or register expressions for every operand. -/
def term {W k n : ℕ} (q : Output) (pub : Param → Fin k) (arg : Fin 18 → Term W k n) : Term W k n :=
  ((formula q).compile pub).instantiate arg

theorem term_binds {W k n : ℕ} (q : Output) (pub : Param → Fin k) (arg : Fin 18 → Term W k n) :
    (term q pub arg).binds = (formula q).work + ∑ i, (arg i).binds := by
  simp [term,Formula.binds_compile]

set_option maxRecDepth 12000 in
theorem work_le (q : Output) : (formula q).work ≤ 10000 := by cases q <;> decide

private theorem operandsOnly (q : Output) {W : ℕ}
    (d₁ d₂ : Param → Word W) (m₁ m₂ : Memory W) (vs : Fin 18 → Word W) :
    (formula q).value d₁ m₁ vs = (formula q).value d₂ m₂ vs := by cases q <;> rfl

/-- The actual native let program computes the natural formula on width-bounded
operands even when the caller's public words and external memory are arbitrary. -/
theorem term_eval {W k n b : ℕ} (q : Output) (pub : Param → Fin k) (arg : Fin 18 → Term W k n)
    (data : Fin k → Word W) (m : Memory W) (input : Fin n → Word W) (vs : Fin 18 → ℕ)
    (argEq : ∀ i,(arg i).eval data m input = (vs i : Word W))
    (smallArg : ∀ i,vs i < 2^b) (margin : 5*b+128 ≤ W) :
    (term q pub arg).eval data m input =
      ((formula q).natural W (fun _ => 0) (fun _ => 0) vs : Word W) := by
  rw [term,Term.eval_instantiate,Formula.eval_compile,funext argEq]
  rw [operandsOnly q (data ∘ pub) (fun _ => (0 : Word W)) m (fun _ => 0)]
  exact Formula.value_eq_natural _ _ _ _ (fits q _ _ _ margin (fun _ => Nat.two_pow_pos _)
    (fun _ => Nat.two_pow_pos _) smallArg)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem hidden_natural (row : Bool) (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (s : Shape)
    (word x y : ℕ) (e : Form) :
    (hidden row e).natural W data mem (vars s word x y) =
      (if row then Prod.fst else Prod.snd) (locate s (e.natural W data mem (vars s word x y))) := by
  let V := e.natural W data mem (vars s word x y)
  let C := s.ticks*s.cpu
  let T := s.layers*(s.rows*s.track)
  let E := (s.rows-1)*s.edge
  by_cases a : V<C <;>
    by_cases b : V-C<T <;>
    by_cases c : V-C-T<E <;>
    by_cases d : V-C-T-E<s.rows*s.copy <;>
    dsimp only [V,C,T,E,vars] at a b c d <;>
    cases row <;>
    simp only [hidden,branch_natural,Bool.false_eq_true,ite_false,ite_true] <;>
    simp [locate,appendAt,Formula.natural,vars,natOp,a,b,c,d]

theorem owner_natural_at (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (s : Shape) (word x y : ℕ) :
    (formula .owner).natural W data mem (vars s word x y) = ownerAt s word y x := by
  simp only [formula,branch_natural]
  rw [hidden_natural]
  simp [ownerAt,appendAt,Formula.natural,vars,natOp]

theorem owner_natural (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (w p r k S f d n x y : ℕ) :
    (formula .owner).natural W data mem (vars (shape w p r k S f d n) w x y) =
      ownerNat w p r k S f d n y x := by
  exact owner_natural_at W data mem (shape w p r k S f d n) w x y

theorem row_natural (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (s : Shape) (word x y : ℕ) :
    (formula .row).natural W data mem (vars s word x y) = (locate s x).1 := by
  exact hidden_natural true W data mem s word x y (R 0)

theorem slot_natural (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (s : Shape) (word x y : ℕ) :
    (formula .slot).natural W data mem (vars s word x y) = (locate s x).2 := by
  exact hidden_natural false W data mem s word x y (R 0)

end ThreeFlat.RAM.TraceOwnerFormula

end OAI
