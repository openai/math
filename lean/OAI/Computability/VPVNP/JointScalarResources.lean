import OAI.Computability.VPVNP.JointScalarMachine

/-!
# Resources of the joint signed scalar checker

The two shared subcircuits process grammar and clock witnesses. The final
layer compares row, exponent and motif words and forces unused banks to zero.
Gate count and all stack budgets are uniform in the query's numerical values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.Resources

open VerifierNetwork ParseGrammar UniversalCountStack
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr.eval Expr.size Expr.mux Expr.size_disjoin_le Expr.not)

variable {n high t W flags clock motif g m q : ℕ}

/-- Size bound for the final Boolean expression that selects the equation and sign, compares
exponents and checks unused witness bits. -/
def finishBound (n high t W flags clock motif g m q L : ℕ) :=
  2*(3*(n+high)+1) + (g+m+t)*(W*3+4) + 4*(flags+clock+motif) +
    Motif.sizeBound q m W motif ((n+high)*3+2) L + 39

theorem zeroWords_size {σ : Type*} (wire : Fin m → Fin W → σ) :
    (zeroWords wire).size ≤ m*(W*3+4)+2 := by
  have h := Expr.size_disjoin_le (List.ofFn fun i => Expr.not (OracleBinaryTarget.expr (wire i) 0))
    (W*3+3) (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      have h := OracleBinaryTarget.expr_size_le (wire i) 0
      change _ + 1 ≤ _
      omega)
  simp only [List.length_ofFn, show W*3+3+1 = W*3+4 by omega] at h
  change _ + 1 ≤ _
  omega

theorem finish_size_le (prod : Fin g → Fin t) (localMap : Fin m → Fin t)
    (tables : Fin q → Motif.Table m) (L : ℕ) (hL : ∀ o, (tables o).length ≤ L) :
    (finish (n := n) (high := high) (W := W) (flags := flags) (clock := clock) (motif := motif)
      prod localMap tables).size ≤ finishBound n high t W flags clock motif g m q L := by
  let raw : Input n high t W flags clock motif → Input n high t W flags clock motif ⊕ Checks := Sum.inl
  let expo := fun i j => raw (exponentWire i j)
  let rows := fun j : Fin q => OracleBinaryTarget.expr (raw ∘ rowWire) (2^n+j.val)
  have hr := Motif.below_size (raw ∘ rowWire) (2^n)
  have hprod := zeroWords_size (expo ∘ prod)
  have hmot := zeroWords_size (expo ∘ localMap)
  have htot := zeroWords_size expo
  have hpadF := allZero_size (raw ∘ flagWire)
  have hpadU := allZero_size (raw ∘ choiceWire)
  have hpadM := allZero_size (raw ∘ motifWire)
  have ht := Motif.expr_size_le tables rows (expo ∘ localMap) (raw polarity) (raw ∘ motifWire)
    ((n+high)*3+2) L (fun j => OracleBinaryTarget.expr_size_le _ _) hL
  dsimp only [raw, rows, expo, Function.comp_def] at *
  simp only [Nat.add_mul] at ht
  simp only [finish, Expr.mux, Expr.size, Function.comp_def, finishBound, Nat.add_mul]
  omega

/-- Combining subcircuits preserves sharing before the final layer is added. -/
theorem frame_size_le (prod : Fin g → Fin t) (localMap : Fin m → Fin t) (tables : Fin q → Motif.Table m)
    (parse : Frame (ParseOracle.Input n t W flags) Unit) (path : Frame (Fin n ⊕ Fin clock) Unit)
    (L : ℕ) (hL : ∀ o, (tables o).length ≤ L) :
    (JointScalar.frame (high := high) (motif := motif) prod localMap tables parse path).size ≤
      parse.size + path.size + finishBound n high t W flags clock motif g m q L := by
  unfold JointScalar.frame
  exact (Frame.step_size_le _ _ _ (fun _ => finish_size_le prod localMap tables L hL)).trans
    (by simp)

/-- The number of query-independent Boolean gates in the joint checker. -/
noncomputable def gateBound (C high motif m q L n t g W : ℕ) :=
  4 * (ParseOracle.gateBound C n W + (VerifierMachine.verifierFrame n).size +
    finishBound n high t W (ParseOracle.flagCount C n) (n^clockExponent) motif g m q L)

/-- Upper bound for the encoded Boolean checker length in terms of its gate count and query and
witness widths. -/
def adviceBound (G U K : ℕ) := (G+2)*(2*(G+U+K+2)+3)

/-- Stack-step bound for testing one witness and advancing the enumerator for a signed
coefficient query. -/
def choiceBound (G U K : ℕ) := 32*(adviceBound G U K + (G+2) + U + K + 1) + 8*K + 9

/-- Bound on the number of bits in each stack during the complete enumeration of coefficient
witnesses. -/
def stackBound (G U K : ℕ) := U + adviceBound G U K + (K+1) + choiceBound G U K

/-- Instantiate the bounds with the grammar incidence circuit and the actual
clocked path verifier at the given length. Both coordinate placements may vary
with the length. The threshold and all query bits are runtime inputs. -/
theorem specialized_le (C n t g W high motif : ℕ) (d : Fin n) (s : ParseOracle.States C n)
    (addr : ParseOracle.Label n n (ParseOracle.States C n) → Fin t) (prod : Fin g → Fin t)
    (localMap : Fin m → Fin t) (tables : Fin q → Motif.Table m) (L : ℕ) (hL : ∀ o, (tables o).length ≤ L) :
    let flags := ParseOracle.Flags n n (ParseOracle.States C n)
    let f := JointScalar.frame (high := high) (motif := motif) prod localMap tables
      (ParseOracle.frame (parseOracleMetadata (ParseOracle.Var n) (ParseOracle.States C n) n d s) addr W)
      (VerifierMachine.verifierFrame n)
    let c := f.circuit ()
    let G := gateBound C high motif m q L n t g W
    let U := queryWidth n high t W
    let K := witnessWidth flags (n^clockExponent) motif
    f.circuitSize () ≤ G ∧ (AdviceCircuit.encode (AdviceCircuit.compile c)).length ≤ adviceBound G U K ∧
      perChoice c ≤ choiceBound G U K ∧ stackLimit c ≤ stackBound G U K ∧
      2^K * perChoice c ≤ 2^(K + choiceBound G U K) := by
  intro flags f c G U K
  have hparse := ParseOracle.checker_frame_size_le d s addr W
  have hframe := frame_size_le (high := high) (motif := motif) prod localMap tables
    (ParseOracle.frame (parseOracleMetadata (ParseOracle.Var n) (ParseOracle.States C n) n d s) addr W)
    (VerifierMachine.verifierFrame n) L hL
  have hflags : Fintype.card (EventCode (ParseOracle.Var n) (ParseOracle.States C n) n) =
      ParseOracle.flagCount C n := ParseOracle.flags_eq_flagCount C n
  have hg : f.circuitSize () ≤ G := by
    apply (Frame.circuitSize_le f ()).trans
    apply Nat.mul_le_mul_left
    rw [← hflags]
    exact hframe.trans (Nat.add_le_add_right (Nat.add_le_add_right (by omega) _) _)
  have ha : (AdviceCircuit.encode (AdviceCircuit.compile c)).length ≤ adviceBound G U K := by
    apply (AdviceCircuit.compile_size c).trans
    change (f.circuitSize () + 2)*(2*(f.circuitSize ()+U+K+2)+3) ≤ _
    unfold adviceBound
    gcongr
  have hc : perChoice c ≤ choiceBound G U K := by
    unfold perChoice choiceBound
    rw [AdviceCircuit.compile_length]
    change 32*((AdviceCircuit.encode (AdviceCircuit.compile c)).length + (f.circuitSize ()+2) + U + K + 1) + 8*K + 9 ≤ _
    omega
  have hs : stackLimit c ≤ stackBound G U K := by
    unfold stackLimit stackBound
    change max (max U _) (K+1) + perChoice c ≤ _
    omega
  refine ⟨hg, ha, hc, hs, ?_⟩
  rw [pow_add 2 K (choiceBound G U K)]
  exact Nat.mul_le_mul_left _ (hc.trans Nat.lt_two_pow_self.le)

variable {width labels productions : ℕ → ℕ}

/-- All parameters except the grammar, its coordinate count, and its exponent
width are fixed independently of the input length. -/
theorem gateBound_polynomial (C high motif m q L : ℕ) (hW : PolynomiallyBounded width)
    (ht : PolynomiallyBounded labels) (hg : PolynomiallyBounded productions) :
    PolynomiallyBounded (fun n => gateBound C high motif m q L n (labels n) (productions n) (width n)) := by
  let hrow := PolynomiallyBounded.id.add (.const high)
  let hflags := ParseOracle.flagCount_polynomial C
  let hclock := PolynomiallyBounded.id.pow clockExponent
  let hcmp := (hW.mul (.const 3)).add (.const 4)
  let hmask := ((hg.add (.const m)).add ht).mul hcmp
  let hpad := (PolynomiallyBounded.const 4).mul ((hflags.add hclock).add (.const motif))
  let hentry := (((PolynomiallyBounded.const m).mul hcmp).add (.const (3*motif))).add (.const 8)
  let hsel := (hrow.mul (.const 3)).add (.const 2)
  let htab := ((PolynomiallyBounded.const q).mul
    ((hsel.add ((PolynomiallyBounded.const L).mul hentry)).add (.const 3))).add (.const 1)
  let hfirst := (PolynomiallyBounded.const 2).mul
    (((PolynomiallyBounded.const 3).mul hrow).add (.const 1))
  let hfinish := ((((hfirst.add hmask).add hpad).add htab).add (.const 39))
  exact (PolynomiallyBounded.const 4).mul (((ParseOracle.gateBound_polynomial C hW).add
    VerifierMachine.verifierFrame_polynomiallyBounded).add hfinish)

/-- Convert gate count and physical word-bank lengths to bounds for the
actual unary-address advice program and the stack enumerator. -/
theorem stack_bounds_polynomial {G U K : ℕ → ℕ}
    (hg : PolynomiallyBounded G) (hu : PolynomiallyBounded U) (hk : PolynomiallyBounded K) :
    PolynomiallyBounded (fun n => adviceBound (G n) (U n) (K n)) ∧
    PolynomiallyBounded (fun n => choiceBound (G n) (U n) (K n)) ∧
    PolynomiallyBounded (fun n => stackBound (G n) (U n) (K n)) ∧
    PolynomiallyBounded (fun n => K n + choiceBound (G n) (U n) (K n)) := by
  let ha := (hg.add (.const 2)).mul (((PolynomiallyBounded.const 2).mul
    (((hg.add hu).add hk).add (.const 2))).add (.const 3))
  let hp := (((PolynomiallyBounded.const 32).mul
    ((((ha.add (hg.add (.const 2))).add hu).add hk).add (.const 1))).add
    ((PolynomiallyBounded.const 8).mul hk)).add (.const 9)
  exact ⟨ha, hp, ((hu.add ha).add (hk.add (.const 1))).add hp, hk.add hp⟩

/-- Polynomial resource bounds for the joint system in the formal coordinate
order, for every exponent width polynomial in the input length. The table
parameters depend only on the fixed motif system. -/
theorem specialized_polynomial (V : Type*) [Fintype V] (C high motif q L : ℕ)
    (hW : PolynomiallyBounded width) :
    let t := fun n => JointLabelSystem.FixedRows.labelTotal V n C
    let g := fun n => JointLabelSystem.FixedRows.productionCount n C
    let G := fun n => gateBound C high motif (Fintype.card V) q L n (t n) (g n) (width n)
    let U := fun n => queryWidth n high (t n) (width n)
    let K := fun n => witnessWidth (ParseOracle.flagCount C n) (n^clockExponent) motif
    PolynomiallyBounded G ∧ PolynomiallyBounded (fun n => adviceBound (G n) (U n) (K n)) ∧
      PolynomiallyBounded (fun n => choiceBound (G n) (U n) (K n)) ∧
      PolynomiallyBounded (fun n => stackBound (G n) (U n) (K n)) ∧
      PolynomiallyBounded (fun n => K n + choiceBound (G n) (U n) (K n)) := by
  intro t g G U K
  have ht : PolynomiallyBounded t := JointLabelSystem.FixedRows.labelTotal_polynomiallyBounded V C
  have hprod : PolynomiallyBounded g := ht.of_le (fun n => by
    have h := JointLabelSystem.FixedRows.labelOrder_length V n C
    change JointLabelSystem.FixedRows.productionCount n C ≤ JointLabelSystem.FixedRows.labelTotal V n C
    omega)
  have hgate : PolynomiallyBounded G := gateBound_polynomial C high motif _ q L hW ht hprod
  have hu : PolynomiallyBounded U := (PolynomiallyBounded.const 1).add
    ((PolynomiallyBounded.id.add (.const high)).add (ht.mul hW))
  have hk : PolynomiallyBounded K := (ParseOracle.flagCount_polynomial C).add
    ((PolynomiallyBounded.id.pow clockExponent).add (.const motif))
  exact ⟨hgate, stack_bounds_polynomial hgate hu hk⟩

/-- The same four polynomial bounds work for every physical query to the
fixed motif and grammar checker at every length `n ≥ 2`. The fourth bounds
the exponent of the exhaustive counting time. -/
theorem checker_polynomial_resources (V I : Type*) [Fintype V] [Fintype I]
    (F : I → MvPolynomial V ℤ) (C : ℕ) (hW : PolynomiallyBounded width) :
    ∃ A B S T : ℕ → ℕ, PolynomiallyBounded A ∧ PolynomiallyBounded B ∧
      PolynomiallyBounded S ∧ PolynomiallyBounded T ∧ ∀ n (hn : 2 ≤ n),
      let c := checker V I F C hn (width n)
      let k := witnessWidth (ParseOracle.Flags n n (ParseOracle.States C n)) (n^clockExponent) (motifWidth V I F)
      (AdviceCircuit.encode (AdviceCircuit.compile c)).length ≤ A n ∧
        perChoice c ≤ B n ∧ stackLimit c ≤ S n ∧ 2^k * perChoice c ≤ 2^(T n) := by
  classical
  let tables := sparseRows V I F
  let L := Finset.univ.sup (fun o => (tables o).length)
  have hL (o) : (tables o).length ≤ L := Finset.le_sup (f := fun o => (tables o).length) (Finset.mem_univ o)
  let high := highWidth I
  let motif := motifWidth V I F
  let labels := fun n => JointLabelSystem.FixedRows.labelTotal V n C
  let productions := fun n => JointLabelSystem.FixedRows.productionCount n C
  let G := fun n => gateBound C high motif (Fintype.card V) (Fintype.card I) L n (labels n) (productions n) (width n)
  let U := fun n => queryWidth n high (labels n) (width n)
  let K := fun n => witnessWidth (ParseOracle.flagCount C n) (n^clockExponent) motif
  obtain ⟨_, ha, hb, hs, ht⟩ := specialized_polynomial V C high motif (Fintype.card I) L hW
  refine ⟨fun n => adviceBound (G n) (U n) (K n), fun n => choiceBound (G n) (U n) (K n),
    fun n => stackBound (G n) (U n) (K n), fun n => K n + choiceBound (G n) (U n) (K n),
    ha, hb, hs, ht, ?_⟩
  intro n hn
  have r := (specialized_le C n (labels n) (productions n) (width n) high motif
    (rootLayer hn) (rootState C hn) (productionAddress V C) (denseProduction V C) (denseLocal V C)
    tables L hL).2
  have hk : K n = witnessWidth (ParseOracle.Flags n n (ParseOracle.States C n)) (n^clockExponent) motif :=
    congrArg (fun k => witnessWidth k (n^clockExponent) motif) (ParseOracle.flags_eq_flagCount C n).symm
  dsimp only
  rw [hk]
  exact r

end JointScalar.Resources

end VPVNP
end Computability
end OAI
