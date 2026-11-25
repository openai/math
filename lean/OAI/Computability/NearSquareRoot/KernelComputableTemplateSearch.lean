import OAI.Computability.NearSquareRoot.KernelComputableWidthCheck
import OAI.Computability.NearSquareRoot.KernelPassComputableEncode
import OAI.Computability.NearSquareRoot.KernelBinaryTemplate
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCode

/-! # Certified search for the finite normalized template in a uniform program

Natural numbers enumerate an arity and a finite list of raw instructions.
The finite shape, call-count and bounded width checks are primitive recursive;
an unbounded search therefore gives a computable function of the exponent.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax
open KernelComputableMatrix

abbrev Raw := ℕ × List Op

def packedCandidate {A : ℕ} : Packed A → Candidate
  | ⟨i,o,p⟩ => if e : o = i then ⟨A,i,e ▸ p⟩ else ⟨0,0,.mix Fin.elim0⟩

@[simp] theorem packedCandidate_square {A W : ℕ} (p : Plan A W W) :
    packedCandidate ⟨W,W,p⟩ = ⟨A,W,p⟩ := dite_eq_left rfl

def interpreted (r : Raw) := packedCandidate (Packed.decode r.1 r.2)

def check (num den A : ℕ) (s : Shape) (u : ℕ → Table) : Prop :=
  5 ≤ A ∧ 2 ≤ s.1.1 ∧ s.1.2 = s.1.1 ∧
  s.2.1^den < s.1.1^den*A^num ∧ allWidths A s.1.1 s.2.2 u

instance (num den A : ℕ) (s : Shape) (u : ℕ → Table) : Decidable (check num den A s u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ allWidths A s.1.1 s.2.2 u))

theorem check_packed {num den A : ℕ} (hd : 0 < den) (p : Packed A) (u : ℕ → Table)
    (hu : ∀ h, p.Represents h (u h)) :
    check num den A p.shape u ↔ (packedCandidate p).Good num den := by
  obtain ⟨i,o,p⟩ := p
  by_cases eq : o = i
  · subst o
    rw [packedCandidate_square p]
    simp only [check, Packed.shape, Candidate.Good, true_and]
    rw [allWidths_iff p u hu]
    constructor
    · rintro ⟨ha,hw,hc,he⟩
      exact ⟨ha,hw,he,(Candidate.calls_lt_iff hd (by omega)).mp hc⟩
    · rintro ⟨ha,hw,he,hc⟩
      exact ⟨ha,hw,(Candidate.calls_lt_iff hd (by omega)).mpr hc,he⟩
  · simp [check, Packed.shape, packedCandidate,eq,Candidate.Good]

theorem primrec_check {X : Type*} [Primcodable X] {num den A : X → ℕ} {s : X → Shape} {t : X → ℕ → Table}
    (hn : Primrec num) (hd : Primrec den) (hA : Primrec A) (hs : Primrec s) (ht : Primrec₂ t) :
    PrimrecPred fun x => check (num x) (den x) (A x) (s x) (t x) := by
  have wi := Primrec.fst.comp (Primrec.fst.comp hs)
  have wo := Primrec.snd.comp (Primrec.fst.comp hs)
  have calls := Primrec.fst.comp (Primrec.snd.comp hs)
  have bound := Primrec.snd.comp (Primrec.snd.comp hs)
  have contract := Primrec.nat_lt.comp (Generator.primrecNatPow.comp calls hd)
    (Primrec.nat_mul.comp (Generator.primrecNatPow.comp wi hd) (Generator.primrecNatPow.comp hA hn))
  exact (Primrec.nat_le.comp (Primrec.const 5) hA).and <|
    (Primrec.nat_le.comp (Primrec.const 2) wi).and <| (Primrec.eq.comp wo wi).and <|
    contract.and (primrec_allWidths hA wi bound ht)

def readRaw (n : ℕ) : Raw := (Encodable.decode n).getD (0,[])

@[simp] theorem readRaw_encode (r : Raw) : readRaw (Encodable.encode r) = r := by rw [readRaw, Encodable.encodek]; rfl

theorem primrec_readRaw : Primrec readRaw :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const _)

/-- Any primitive-recursive numerical evaluator with the represented entry
semantics supplies a common template selector. Each selected literal opcode
list interprets to a correct program with the strict child-call saving. -/
theorem select_of_evaluation (u : Raw → ℕ → Table) (hu : Primrec₂ u)
    (ue : ∀ r h, (Packed.decode r.1 r.2).Represents h (u r h))
    (num den : ℕ → ℕ) (hnum : Primrec num) (hden : Primrec den)
    (hd : ∀ j, 0 < den j) (hθ : ∀ j, 1/2 < (num j : ℝ)/(den j)) :
    ∃ select : ℕ → Raw, Computable select ∧ ∀ j, (interpreted (select j)).Good (num j) (den j) := by
  let valid (j k : ℕ) :=
    let r := readRaw k
    check (num j) (den j) r.1 ((Shape.algebra r.1).parse r.2) (u r)
  let (j k : ℕ) : Decidable (valid j k) := inferInstanceAs (Decidable (check _ _ _ _ _))
  have hv : PrimrecRel valid := by
    have hr := primrec_readRaw.comp (Primrec.snd (α := ℕ) (β := ℕ))
    exact primrec_check (hnum.comp Primrec.fst) (hden.comp Primrec.fst) (Primrec.fst.comp hr)
      (Shape.primrec_algebra.comp (Primrec.fst.comp hr) (Primrec.snd.comp hr))
      (hu.comp (hr.comp Primrec.fst) Primrec.snd).to₂
  have he (j k : ℕ) : valid j k ↔ (interpreted (readRaw k)).Good (num j) (den j) := by
    dsimp only [valid, interpreted]
    rw [← Packed.decode_shape]
    exact check_packed (hd j) _ _ (ue _)
  have hex (j : ℕ) : ∃ k : ℕ, decide (valid j k) = true := by
    obtain ⟨⟨A,W,p⟩,hg⟩ := exists_good_template (hθ j)
    let r : Raw := (A,Packed.encode p)
    refine ⟨Encodable.encode r,decide_eq_true ((he _ _).mpr ?_)⟩
    rw [readRaw_encode]
    change (packedCandidate (Packed.decode A (Packed.encode p))).Good _ _
    rw [Packed.decode_encode,packedCandidate_square]
    exact hg
  obtain ⟨f,hf,hv⟩ := Generator.first_certificate (fun j k => decide (valid j k)) hv.decide.to_comp hex
  exact ⟨fun j => readRaw (f j),primrec_readRaw.to_comp.comp hf,
    fun j => (he _ _).mp (of_decide_eq_true (hv j).1)⟩

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
