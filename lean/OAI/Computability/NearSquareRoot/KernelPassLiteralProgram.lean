import OAI.Computability.NearSquareRoot.KernelPassComputableEncode
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCode
import OAI.Computability.NearSquareRoot.ScheduleGeneratorExecution

/-! # Generating the literal finite instruction list on tapes

The first output numeral records the arity. Each subsequent numeral encodes
one instruction, including every dyadic coefficient and every signature mask.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

open Turing.ToPartrec IntegerMultiplication

abbrev RawTemplate := ℕ × List Op

def literalWord (s : RawTemplate) : List ℕ := s.1 :: s.2.map Encodable.encode

def literalRead (w : List ℕ) : RawTemplate :=
  (w.getD 0 0, w.tail.map fun n => (Encodable.decode (α := Op) n).getD (0,[],[]))

theorem primrec_literalWord : Primrec literalWord :=
  Primrec.list_cons.comp Primrec.fst (Primrec.list_map Primrec.snd (Primrec.encode.comp Primrec.snd).to₂)

theorem primrec_literalRead : Primrec literalRead := by
  have h := Primrec.option_getD.comp (Primrec.decode (α := Op)) (Primrec.const (0,[],[]))
  exact ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 0)).pair
    (Primrec.list_map Primrec.list_tail (h.comp Primrec.snd).to₂)

@[simp] theorem literalRead_word (s : RawTemplate) : literalRead (literalWord s) = s := by
  obtain ⟨A,ops⟩ := s
  change (A, (ops.map Encodable.encode).map _) = (A,ops)
  congr 1
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons, Encodable.encodek, Option.getD_some, ih]

/-- The literal template emitted for a typed pass decodes to the same pass. -/
theorem literalWord_plan {A i o : ℕ} (p : Plan A i o) :
    let t := literalRead (literalWord (A,Packed.encode p))
    Packed.decode t.1 t.2 = ⟨i,o,p⟩ := by
  change Packed.decode A (literalRead (literalWord (A,Packed.encode p))).2 = _
  rw [congrArg Prod.snd (literalRead_word (A,Packed.encode p)), Packed.decode_encode]
  rfl

/-- A single finite-control generator produces the whole literal list for
every unary family index and halts on the actual four tapes. -/
theorem literal_generator (s : ℕ → RawTemplate) (hs : Computable s) :
    ∃ c : Turing.ToPartrec.Code, ∀ i,
      let w := Generator.unaryInput i
      let out := literalWord (s i)
      c.eval w = Part.some out ∧ ∃ t,
        Trace (TM.advance (Generator.rule c)) (Generator.initial c w) t (Generator.finalCfg c w out) ∧
        TM.advance (Generator.rule c) (Generator.finalCfg c w out) = none ∧
        VisitsAtMost (Generator.rule c) (Generator.initial c w) t (4*(2*t+1)) := by
  obtain ⟨c,hc⟩ := Generator.exists_unary_list_code _ (primrec_literalWord.to_comp.comp hs)
  exact ⟨c, fun i => ⟨hc i, Generator.code_execution c _ _ (Part.eq_some_iff.mp (hc i))⟩⟩

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
