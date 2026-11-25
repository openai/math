import OAI.LinearAlgebra.MatrixExponent.Packing.Frame

/-!
# The graph interface to local concentration

Each index in `Cell h` identifies an independent block. Host positions
name cells and each station belongs to one cell of one block. The input
has positive arities and integral packets of width `R`. The output
reserves individual host slots for the stations and is padded to units
of width `u` before the beats.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

structure Input (F : Type) (x y : Wire) (h D T R g : ℕ) (W : ℝ) where
  V : Type
  [fv : Fintype V]
  diagram : Diagram F x y
  place : diagram.V → V × Cell h
  adj : V → Finset V
  sym : ∀ v z, z ∈ adj v → v ∈ adj z
  degree : ∀ v, (adj v).card ≤ g
  edge : ∀ e, let q := place (diagram.source e)
    let p := place (diagram.target e)
    p.2 = q.2 ∧ (p.1 = q.1 ∨ p.1 ∈ adj q.1)
  loopless : ∀ e, diagram.source e ≠ diagram.target e
  positive : ∀ v, 0 < diagram.arity v
  width : ∀ v w, R ∣ Fintype.card {e // diagram.source e = v ∧ diagram.target e = w}
  mobile : diagram.V → Prop
  ext : ∀ q, ¬mobile (portEnd diagram q)
  occupied : (univ.image place).card * D * T ≤ W
  immobile : Fintype.card {v // ¬mobile v} * D * T ≤ W
  count : ∀ p, Fintype.card {v // place v = p} ≤ 100 * D
  mass : ∀ p, push place (fun v => (diagram.arity v : ℝ)) p ≤ 100 * (D : ℝ) * T
  squares : (∑ v, (diagram.arity v : ℝ) ^ 2) ≤ W * T
  /-- Optional local station and host keys for deterministic numbering. -/
  ranks : Option ((diagram.V → ℕ) × (V → ℕ)) := none

attribute [instance] Input.fv

structure LocalTerm (F : Type) (x y : Wire) (h u : ℕ) where
  V : Type
  [fv : Fintype V]
  diagram : Diagram F x y
  freeze : Freeze diagram
  frame : freeze.Frame V h
  one : Function.Injective frame.place
  width : ∀ v w, u ∣ Fintype.card {e // diagram.source e = v ∧ diagram.target e = w}
  charge : diagram.V → ℝ
  cover : ∀ v, diagram.arity v ≤ charge v
  floor : ∀ v, u ≤ charge v

attribute [instance] LocalTerm.fv

variable {F : Type} {x y : Wire} {h D T R g u : ℕ} {W : ℝ}

/-- The graph and arity estimates needed from one summand. Here `D=2^d`
in applications. All implicit constants are bounded by `C`. -/
structure Concentrated (P : Input F x y h D T R g W) (Q : LocalTerm F x y h u)
    (C d ℓ : ℕ) : Prop where
  cells : Fintype.card Q.V ≤ D ^ C * Fintype.card P.V
  coreDegree : ∀ v, (Q.frame.C v).card ≤ C
  fullDegree : ∀ v, (Q.frame.N v).card ≤ D ^ C
  frozenCount : Fintype.card Q.freeze.Fixed * D * T ≤ C * W
  frozenMax : ∀ v : Q.freeze.Fixed, Q.charge v.val ≤ (C : ℝ) * D * T
  frozenSquare : (∑ v : Q.freeze.Fixed, Q.charge v.val ^ 2) ≤ C * W * T
  coreMax : ∀ v : Q.freeze.Core, Q.charge v.val * (D : ℝ) ^ ℓ ≤ T
  coreSum : (∑ v : Q.freeze.Core, Q.charge v.val) ≤ C * W * (1 + (d : ℝ)) ^ 2

/-- The exact expansion and control-index count. Algorithmic locality
of the chosen terms is an additional requirement for realizing the sum. -/
def LocalExpansion [Field F] (P : Input F x y h D T R g W) (u C d ℓ A : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (Q : I → LocalTerm F x y h u) (c : I → F),
    Fintype.card I ≤ 2 ^ (A * (1 + Nat.clog 2 (T + 1)) * (univ.image P.place).card) ∧
    (∀ x y, ∑ i, c i * (Q i).diagram.eval x y = P.diagram.eval x y) ∧
    ∀ i, Concentrated P (Q i) C d ℓ

end OAI.LinearAlgebra.MatrixExponent.Rounds

namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Filter

/-- Uniform local concentration uses a fixed finite extension for
planting and polynomially many field points for the motions. -/
def LocalLaw (k : Type) [Field k] (ℓ : ℕ) : Prop :=
  ∀ g : ℕ, 0 < g → ∃ C : ℕ, ∀ᶠ d : ℕ in atTop,
    let D := 2 ^ d
    ∃ (A : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
      ∀ᶠ T : ℕ in atTop, ∃ R : ℕ, 0 < R ∧ R * D ^ 2 ≤ T ∧
        ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra L K),
          A * (1 + T) ^ A ≤ Fintype.card K → ∀ u : ℕ, 0 < u → u * D ^ C ≤ T →
          ∀ (x y : Wire) (h : ℕ) (W : ℝ) (P : Input K x y h D T R g W), LocalExpansion P u C d ℓ A

end OAI.LinearAlgebra.MatrixExponent.Rounds
