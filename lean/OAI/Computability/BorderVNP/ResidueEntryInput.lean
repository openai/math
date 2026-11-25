import OAI.Computability.BorderVNP.ResidueEntryBasis
import OAI.Computability.BorderVNP.ResidueEntryCircuitGadget
import OAI.Computability.BorderVNP.ResidueEntryFieldGuess
import OAI.Computability.BorderVNP.ResidueEntryFrame

/-! # Register inputs of the shared residue-entry verifier

The query supplies the three offset exponent vectors, the row and column basis indices,
and the gadget multiplicities. The guess supplies the interpolation grid and the final
threshold. All selections are from this same numbered tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryInput

open ExactQuantumFactoring BooleanNetwork BitArithmetic
open ResidueIndex ResidueFourier ResidueEntryField ResidueBox

/-- Query bits. The Boolean selector labels the row address by false and the column by true. -/
abbrev Query (σ : Type*) (idx D : ℕ) (J : Type*) (m : ℕ) :=
  Raw σ idx ⊕ ((Bool × Fin (Nat.clog 2 D)) ⊕ J × Fin m)

/-- Guess bits. Each coordinate gets one extension-field word, followed by a threshold word. -/
abbrev Guess (σ : Type*) (d w b : ℕ) := (Option σ × Fin (d*w)) ⊕ Fin b

/-- Named wires of the joint query and guess. -/
abbrev Input (σ : Type*) (idx D : ℕ) (J : Type*) (m d w b : ℕ) :=
  Query σ idx D J m ⊕ Guess σ d w b

variable {σ J K : Type*} {idx D m d w b p : ℕ}

/-- Encode an in-range row or column in the minimal little-endian address width. -/
def addressWord (i : Fin D) : Fin (Nat.clog 2 D) → Bool :=
  fun j => (BitVec.ofNat (Nat.clog 2 D) i.val).getLsbD j.val

/-- Decoding the address bits gives the original table index, including for a singleton table. -/
theorem addressWord_value (i : Fin D) : value (addressWord i) = i.val := by
  unfold value addressWord
  rw [bitsValue_bits,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  exact i.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two D)

/-- Serialize all fixed query fields, with multiplicities in little-endian order. -/
def encodeQuery (idx H m : ℕ) (e μ k : Exponent σ) (row col : Fin D) (δ : J → ℕ) :
    Query σ idx D J m → Bool :=
  Sum.elim (encode idx H e μ k) (Sum.elim
    (fun (side,j) => addressWord (if side then col else row) j)
    (fun (j,i) => (δ j).testBit i.val))

/-- Serialize the guessed grid and threshold words. -/
def encodeGuess (grid : Option σ → Fin (d*w) → Bool) (y : Fin b → Bool) :
    Guess σ d w b → Bool := Sum.elim (fun (i,j) => grid i j) y

/-- Row or column address on the joint tape. -/
def addressWire (side : Bool) (j : Fin (Nat.clog 2 D)) : Input σ idx D J m d w b := .inl (.inr (.inl (side,j)))

/-- A bit of one guessed grid coordinate. -/
def gridWire (i : Option σ) (j : Fin (d*w)) : Input σ idx D J m d w b := .inr (.inl (i,j))

/-- A bit of the final threshold. -/
def thresholdWire (j : Fin b) : Input σ idx D J m d w b := .inr (.inr j)

/-- Number a named assignment by the finite equivalence used by the Boolean interpreter. -/
noncomputable def number {S : Type*} [Fintype S] (a : S → Bool) : Fin (Fintype.card S) → Bool :=
  a ∘ (Fintype.equivFin S).symm

/-- Zero-cost selection of named wires from a numbered input. -/
noncomputable def route {S : Type*} [Fintype S] {l : ℕ} (f : Fin l → S) :
    BooleanNetwork (Fintype.card S) l := select (Fintype.equivFin S ∘ f)

/-- Reading selected named wires commutes with numbering. -/
theorem route_eval {S : Type*} [Fintype S] {l : ℕ} (f : Fin l → S) (a : S → Bool) :
    (route f).eval (number a) = a ∘ f := by
  funext i
  simp [route,number]

/-- Named selections introduce no gates. -/
theorem route_count {S : Type*} [Fintype S] {l : ℕ} (f : Fin l → S) :
    (route f).net.count = 0 := rfl

variable [Fintype σ] [Fintype J]

local notation "Tape" => Input σ idx D J m d w b

private noncomputable def indexBit (q H width : ℕ) (pin : Out σ idx) :
    BooleanNetwork (Fintype.card Tape) 1 :=
  let raw (j : Fin (Fintype.card (Raw σ idx))) : Tape :=
    .inl (.inl ((Fintype.equivFin _).symm j))
  ((route raw).comp (ResidueEntryFrame.network (frame σ q H width idx))).rewire
    fun _ => Fintype.equivFin _ pin

private theorem indexBit_eval (q H width : ℕ) (pin : Out σ idx) (a : Tape → Bool) :
    (indexBit q H width pin).eval (number a) 0 =
      (frame σ q H width idx).eval (fun j => a (.inl (.inl j))) pin := by
  simp only [indexBit, eval_rewire, Function.comp_apply, eval_comp, route_eval]
  exact ResidueEntryFrame.network_eval (frame σ q H width idx) (fun j => a (.inl (.inl j))) pin

private theorem indexBit_count (q H width : ℕ) (pin : Out σ idx) :
    (indexBit (D := D) (J := J) (m := m) (d := d) (w := w) (b := b) q H width pin).net.count ≤
      4 * ResidueIndex.budget (Fintype.card (Option σ)) idx := by
  simp only [indexBit,count_rewire,count_comp,route_count,zero_add]
  exact (ResidueEntryFrame.network_count _).trans (Nat.mul_le_mul_left 4 (frame_size ..))

variable [Field K] [Fact p.Prime] [Algebra (ZMod p) K]

private noncomputable def liftBit {n : ℕ} (w : ℕ) (B : Module.Basis (Fin d) (ZMod p) K)
    (v : BooleanNetwork n 1) : BooleanNetwork n (d*w) :=
  wordMux v (fieldConst n w B 1) (fieldConst n w B 0)

private theorem liftBit_value {n : ℕ} (hp : p < 2^w) (B : Module.Basis (Fin d) (ZMod p) K)
    (v : BooleanNetwork n 1) (x : Fin n → Bool) :
    Represents B ((liftBit w B v).eval x) (if v.eval x 0 then 1 else 0) := by
  rw [liftBit,wordMux_eval]
  split <;> exact fieldConst_value hp B _ x

private theorem liftBit_count {n : ℕ} (B : Module.Basis (Fin d) (ZMod p) K)
    (v : BooleanNetwork n 1) :
    (liftBit w B v).net.count ≤ v.net.count + 2*(d*w*w) + 7*(d*w) := by
  rw [liftBit,wordMux_count]
  have := fieldConst_count (n := n) (w := w) B (1 : K)
  have := fieldConst_count (n := n) (w := w) B (0 : K)
  omega

/-- Each input of the single arithmetic entry circuit is read as a field register. The
old scalar slot is one because the gadget multiplicities provide the scalar separately. -/
noncomputable def fieldNet (q H width : ℕ) (B : Module.Basis (Fin d) (ZMod p) K)
    (u : Fin D → K) : GadgetInput σ idx J m → BooleanNetwork (Fintype.card Tape) (d*w)
  | .inl (.inl i) => route (gridWire i)
  | .inl (.inr (.inl (i,j))) => liftBit w B (indexBit q H width (.inr (i,j)))
  | .inl (.inr (.inr t)) => Fin.cases (liftBit w B (indexBit q H width (.inl ())))
      (Fin.cases (fieldConst _ w B 1) (fun _ =>
        (route (addressWire false)).comp (ResidueEntryBasis.basisLookup w B u))) t
  | .inr (j,i) => liftBit w B (route fun _ => (.inl (.inr (.inr (j,i))) : Tape))

/-- Every arithmetic input has its required formal assignment under a decoded grid guess. -/
theorem fieldNet_represents (q H width : ℕ) (hp : p < 2^w)
    (B : Module.Basis (Fin d) (ZMod p) K) (u : Fin D → K)
    (e μ k : Exponent σ) (row col : Fin D) (δ : J → ℕ)
    (grid : Option σ → Fin (d*w) → Bool) (y : Fin b → Bool) (x : Option σ → Kˣ)
    (hx : ∀ i, Represents B (grid i) (x i : K)) (v : GadgetInput σ idx J m) :
    Represents B ((fieldNet q H width B u v).eval
      (number (Sum.elim (encodeQuery idx H m e μ k row col δ) (encodeGuess grid y))))
      ((Sum.elim (queryAssignment q H width idx x (encode idx H e μ k) 1 (u row))
        (fun (j,i) => if (δ j).testBit i.val then 1 else 0)) v) := by
  let a : Tape → Bool := Sum.elim (encodeQuery idx H m e μ k row col δ) (encodeGuess grid y)
  have hidx (j : Out σ idx) : (indexBit q H width j).eval (number a) 0 =
      (frame σ q H width idx).eval (encode idx H e μ k) j := indexBit_eval ..
  rcases v with (i | (⟨i,j⟩ | t)) | ⟨j,i⟩
  · change Represents B ((route (gridWire i)).eval (number a)) (x i : K)
    rw [route_eval]; exact hx i
  · change Represents B ((liftBit w B (indexBit q H width (.inr (i,j)))).eval (number a))
      (if (frame σ q H width idx).eval (encode idx H e μ k) (.inr (i,j)) then 1 else 0)
    rw [← hidx]
    exact liftBit_value hp B _ _
  · fin_cases t
    · change Represents B ((liftBit w B (indexBit q H width (.inl ()))).eval (number a))
        (if (frame σ q H width idx).eval (encode idx H e μ k) (.inl ()) then 1 else 0)
      rw [← hidx]
      exact liftBit_value hp B _ _
    · exact fieldConst_value hp B 1 (number a)
    · change Represents B (((route (addressWire false)).comp _).eval (number a)) (u row)
      rw [eval_comp,route_eval]
      exact ResidueEntryBasis.basisLookup_at hp B u _ row (addressWord_value row)
  · let v : BooleanNetwork (Fintype.card Tape) 1 :=
      route fun _ => (.inl (.inr (.inr (j,i))) : Tape)
    change Represents B ((liftBit w B v).eval (number a))
      (if (δ j).testBit i.val then 1 else 0)
    have he : v.eval (number a) 0 = (δ j).testBit i.val := by unfold v; rw [route_eval]; rfl
    rw [← he]
    exact liftBit_value hp B _ _

/-- Accepted grid words supply precisely the decoded field registers of the query. -/
theorem fieldNet_represents_valid (q H width : ℕ) (hp : p < 2^w)
    (B : Module.Basis (Fin d) (ZMod p) K) (u : Fin D → K)
    (e μ k : Exponent σ) (row col : Fin D) (δ : J → ℕ)
    (grid : Option σ → Fin (d*w) → Bool) (y : Fin b → Bool) (x : Option σ → Kˣ)
    (hv : ∀ i, validLimbs p (limbWords d w (grid i)))
    (hx : ∀ i, (x i : K) = unpackScalar B (limbWords d w (grid i))) (v : GadgetInput σ idx J m) :
    Represents B ((fieldNet q H width B u v).eval
      (number (Sum.elim (encodeQuery idx H m e μ k row col δ) (encodeGuess grid y))))
      ((Sum.elim (queryAssignment q H width idx x (encode idx H e μ k) 1 (u row))
        (fun (j,i) => if (δ j).testBit i.val then 1 else 0)) v) :=
  fieldNet_represents q H width hp B u e μ k row col δ grid y x
    (fun i => hx i ▸ represents_unpack B _ (hv i)) v

/-- Gate bound for any one input register, with no field-cardinality enumeration. -/
def budget (h idx D d w : ℕ) : ℕ :=
  4*ResidueIndex.budget h idx + 2*(d*w*w) + 7*(d*w) +
    ResidueEntryBasis.lookupBudget D (d*w) (Nat.clog 2 D) (d*w)

/-- Binary selection of a grid word, index bit, field-basis element or multiplicity bit
costs at most the common polynomial input-register budget. -/
theorem fieldNet_count (q H width : ℕ) (B : Module.Basis (Fin d) (ZMod p) K)
    (u : Fin D → K) (v : GadgetInput σ idx J m) :
    (fieldNet (w := w) (b := b) q H width B u v).net.count ≤ budget (Fintype.card (Option σ)) idx D d w := by
  have hb (j : Out σ idx) := indexBit_count (D := D) (J := J) (m := m) (d := d) (w := w)
    (b := b) q H width j
  let h := Fintype.card (Option σ)
  have hbit (j : Out σ idx) :
      (liftBit w B (indexBit (D := D) (J := J) (m := m) (d := d) (w := w) (b := b)
        q H width j)).net.count ≤ budget h idx D d w := by
    apply (liftBit_count B _).trans
    unfold budget; have := hb j; dsimp [h]; omega
  rcases v with (i | (⟨i,j⟩ | t)) | ⟨j,i⟩
  · exact Nat.zero_le _
  · exact hbit _
  · fin_cases t
    · exact hbit _
    · exact (fieldConst_count B 1).trans (by unfold budget; omega)
    · change ((route (addressWire false : _ → Tape)).comp _).net.count ≤ _
      rw [count_comp,route_count,zero_add]
      exact (ResidueEntryBasis.basisLookup_count B u).trans (by unfold budget; omega)
  · apply (liftBit_count B _).trans
    rw [route_count]; unfold budget; omega

/-- Polynomial dimensions and word widths give a polynomial input-register gate count. -/
theorem polynomiallyBounded_budget {h idx D d w : ℕ → ℕ} (hh : VPVNP.PolynomiallyBounded h)
    (hi : VPVNP.PolynomiallyBounded idx) (hD : VPVNP.PolynomiallyBounded D)
    (hd : VPVNP.PolynomiallyBounded d) (hw : VPVNP.PolynomiallyBounded w) :
    VPVNP.PolynomiallyBounded fun n => budget (h n) (idx n) (D n) (d n) (w n) := by
  let c := VPVNP.PolynomiallyBounded.const
  let dw := hd.mul hw
  let lookup := dw.mul ((hD.mul ((((c 97).mul hD.clog).add dw).add (c 26))).add (c 1))
  exact ((((c 4).mul (ResidueIndex.polynomiallyBounded_budget hh hi)).add
    ((c 2).mul (dw.mul hw))).add ((c 7).mul dw)).add lookup

end ResidueEntryInput

end BorderVNP
end Computability
end OAI
