import OAI.Computability.VPVNP.MacaulayAdvicePreload

/-! # Initial advice of the augmented Macaulay matrix reader

The private decoder words specify the number of original equations, affine
pins and multiplier monomials. Its two scalar banks contain the signed grammar
coefficient circuit and the actual pin mask and field values. Both are reusable
across all row and column queries. Scratch decoder registers may change, but
their widths and the exact leaf data are preserved by the ready predicate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.BaseAdvice

open RAMTape UniversalCountStack SliceArithmetic RadicalCertificate.MonomialIndex BurstRAM

variable {F : Type*} {p e t eqs : ℕ}

/-- The source radix is the multiplier degree for an equation, and the point
bound for an appended powered monomial. The column radix is common. -/
def inputs (S : QueryData t eqs F) (power : Bool) : PairCall.Inputs where
  arity := t
  degree := fun column ↦ if column then S.columnDegree else if power then S.pointBound else S.multiplierDegree
  ordinal := fun _ ↦ 0
  scale := if power then S.power else 1
  mark := 0

variable [Fact p.Prime]

/-- Encode the extension-field element zero or one selected by the Boolean flag, using v bits
per ground-field coordinate. -/
def scalars (c : Vector p e) (v : ℕ) (bit : Bool) : List Bool :=
  Engine.scalar v (if bit then (1 : Scalar c) else 0)

/-- The immutable leaf bank for the integer, affine and powered-monomial arms. -/
def leaf (S : QueryData t eqs F) (L : JointScalar.Leaf.Layout) (c : Vector p e) (w v : ℕ)
    (pins : Finset (Fin t)) (values : Fin t → Scalar c) : Stacks (Arms.Leaf Arms.CoefficientPort) :=
  Arms.storage w (inputs S) Arms.blank Arms.blank (scalars c v) (Arms.coefficientAdvice L w v pins values)

/-- Canonical initial decoder registers. The two externally aliased addresses
and all dispatch outputs start at zero. -/
def registers (w originals pins multiples : ℕ) (j : MacaulayRowDispatch.Reg) : Word w :=
  if h : j.val < 8 then Fin.ofNat _ (MacaulayRowDispatch.inputs 0 0 originals pins multiples ⟨j.val,h⟩) else 0

theorem registers_params {w orig pins multiple : ℕ} (h₁ : orig < 2^w) (h₂ : pins < 2^w)
    (h₃ : multiple < 2^w) : Params orig pins multiple (registers w orig pins multiple) := by
  intro i _
  have hi : (MacaulayRowDispatch.inReg i).val = i.val := rfl
  have hv : (⟨(MacaulayRowDispatch.inReg i).val, hi ▸ i.isLt⟩ : Fin 8) = i := Fin.ext hi
  rw [registers, dite_eq_left (hi ▸ i.isLt), hv, Fin.val_ofNat, Nat.mod_eq_of_lt]
  fin_cases i <;> simp [MacaulayRowDispatch.inputs, h₁, h₂, h₃]

/-- Physical working ports for the row decoder together with the coefficient-reader advice. -/
abbrev RawPort := Work (Arms.Leaf Arms.CoefficientPort)

/-- Initialize the row decoder with the equation, pin and multiplier counts and install the
scalar advice used by all row queries. -/
def initial (originals : ℕ) (S : QueryData t eqs F) (L : JointScalar.Leaf.Layout) (c : Vector p e) (w v : ℕ)
    (pins : Finset (Fin t)) (values : Fin t → Scalar c) : Stacks RawPort :=
  auxBank (registers w originals t (size t S.multiplierDegree)) (leaf S L c w v pins values)

/-- The decoder has the required counts and bounded register widths, and its leaf bank still
holds the specified coefficient and pin advice. -/
def ready (originals : ℕ) (S : QueryData t eqs F) (L : JointScalar.Leaf.Layout) (c : Vector p e) (w v : ℕ)
    (pins : Finset (Fin t)) (values : Fin t → Scalar c) : Stacks RawPort → Prop :=
  Ready w originals t (size t S.multiplierDegree) (· = leaf S L c w v pins values)

theorem initial_ready (originals : ℕ) (S : QueryData t eqs F) (L : JointScalar.Leaf.Layout) (c : Vector p e)
    (w v : ℕ) (pins : Finset (Fin t)) (values : Fin t → Scalar c) (ho : originals < 2^w)
    (ht : t < 2^w) (hm : size t S.multiplierDegree < 2^w) :
    ready originals S L c w v pins values (initial originals S L c w v pins values) :=
  ⟨_, _, registers_params ho ht hm, rfl, rfl⟩

/-- Every state permitted at a repeated-query boundary satisfies the same height
bound. The encoded matrix dimensions themselves may be exponential. -/
theorem ready_length {originals w v A : ℕ} (S : QueryData t eqs F) (L : JointScalar.Leaf.Layout)
    (c : Vector p e) (pins : Finset (Fin t)) (values : Fin t → Scalar c)
    (pre : Arms.Preload (w := w) A (inputs S) (scalars c v) (Arms.coefficientAdvice L w v pins values))
    (s : Stacks RawPort) (h : ready originals S L c w v pins values s) (k : RawPort) : (s k).length ≤ A := by
  obtain ⟨rs, _, _, rfl, rfl⟩ := h
  exact Arms.frame_bound rs [] (inputs S) Arms.blank Arms.blank (scalars c v) (Arms.coefficientAdvice L w v pins values)
    pre.words (Nat.zero_le _) pre.arity (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _) pre.scalars pre.payload (.aux k)

/-- The physical ready cap follows from the common reader plan before the
particular field and its affine pins are chosen. -/
theorem ready_length_uniform {originals w v E V signedSpace : ℕ} (P : ReaderPlan) (S : QueryData t eqs F)
    (L : JointScalar.Leaf.Layout) (c : Vector p e) (pins : Finset (Fin t)) (values : Fin t → Scalar c)
    (ht : P.arity = t) (he : e ≤ E) (hv : v ≤ V) (hs : JointScalar.Leaf.bankSize L w (t*w) ≤ signedSpace)
    (s : Stacks RawPort) (h : ready originals S L c w v pins values s) (k : RawPort) :
    (s k).length ≤ P.live E V w signedSpace :=
  ready_length S L c pins values (Arms.coefficientAdvice_preload ht he hv hs pins values (inputs S)
    (fun _ ↦ rfl) (scalars c v) (fun b ↦ (Engine.scalar_length v (if b then (1 : Scalar c) else 0)).le)) s h k

end RankQuery.Stack.MacaulayRead.BaseAdvice

end VPVNP
end Computability
end OAI
