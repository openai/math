import OAI.Computability.NearSquareRoot.ScheduleGeneratorCompactRows
import OAI.Computability.NearSquareRoot.ScheduleGeneratorOneHot

/-! # Uniform generation of output-compactor rows for one-hot word alphabets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.CompactRows
open IntegerMultiplication CommonAlphabet Numbering

/-- Decode a complete ternary buffer using the first set marker. A separate finite
output classifier recognizes the candidate's zero and one output symbols. -/
def classify (w blank : ℕ) (decode : ℕ → ℕ) (buf : ℕ) :=
  decode (OneHot.decode blank (decodeBase 3 buf w))

theorem classify_eq {A : Type} (a : Numbering A) (blank : A) (decode : A → Option Bool)
    (out : ℕ → ℕ) (hout : ∀ x, out (a.equiv x).val = rankTernary (decode x))
    (b : Letters a.size) :
    classify a.size (a.equiv blank).val out (rankBuf b) =
      rankTernary (decode ((oneHot a.equiv blank).dec b)) := by
  unfold classify
  have h := decodeBase_arrow_symm (fin a.size) ternary ((buffer a.size).equiv b)
  change decodeBase 3 (rankBuf b) a.size = _ at h
  simp only [buffer, Equiv.symm_apply_apply] at h
  rw [h, OneHot.decode_oneHot_all, hout]

theorem computable_classify {w blank : ℕ → ℕ} {decode : ℕ → ℕ → ℕ}
    (hw : Computable w) (hb : Computable blank) (hd : Computable₂ decode) :
    Computable₂ fun j n => classify (w j) (blank j) (decode j) n := by
  have unpack : Primrec fun p : ℕ × ℕ => decodeBase 3 p.2 p.1 :=
    primrec_decodeBase (Primrec.const 3) Primrec.snd Primrec.fst
  have digits : Computable fun p : ℕ × ℕ => decodeBase 3 p.2 (w p.1) :=
    Computable.comp (f := fun p : ℕ × ℕ => decodeBase 3 p.2 p.1)
      (g := fun p : ℕ × ℕ => (w p.1,p.2)) unpack.to_comp ((hw.comp Computable.fst).pair Computable.snd)
  have symbol : Computable fun p : ℕ × ℕ => OneHot.decode (blank p.1) (decodeBase 3 p.2 (w p.1)) :=
    OneHot.primrec_decode.to_comp.comp (hb.comp Computable.fst) digits
  change Computable fun p : ℕ × ℕ => decode p.1 (OneHot.decode (blank p.1) (decodeBase 3 p.2 (w p.1)))
  exact hd.comp Computable.fst symbol

/-- The four-letter public compactor contributes computably many states and a uniformly
computable transition table for every effective family of candidate output classifiers. -/
theorem compile_family {A : ℕ → Type} (a : ∀ j, Numbering (A j)) (blank : ∀ j, A j)
    (decode : ∀ j, A j → Option Bool) (out : ℕ → ℕ → ℕ)
    (ha : Computable fun j => (a j).size)
    (hb : Computable fun j => ((a j).equiv (blank j)).val) (hd : Computable₂ out)
    (hout : ∀ j x, out j ((a j).equiv x).val = rankTernary (decode j x)) :
    let code := fun j => oneHot (a j).equiv (blank j)
    let rows := fun j => row (a j).size (classify (a j).size ((a j).equiv (blank j)).val (out j))
    Computable (fun j => (compact (a j).size).size) ∧ Computable₂ rows ∧ ∀ j s top,
      rows j (rankState s,((bool.arrow publicLetter).equiv top).val) =
        (Compact.rule (code j) Option.join (decode j) Public.bit Option.isNone s top).map fun z =>
          (rankState z.1,((bool.arrow (publicLetter.prod Numbering.move)).equiv z.2).val) := by
  have arity : Primrec fun w : ℕ => 3^w*w + (3+w) + 2 :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp
      (KernelComputableAddress.primrec_pow (Primrec.const 3) Primrec.id) Primrec.id)
      (Primrec.nat_add.comp (Primrec.const 3) Primrec.id)) (Primrec.const 2)
  exact ⟨arity.to_comp.comp ha, computable_row ha (computable_classify ha hb hd),
    fun j => row_eq _ _ _ (classify_eq (a j) (blank j) (decode j) (out j) (hout j))⟩

end Generator.CompactRows

end NearSquareRoot
end Computability
end OAI
