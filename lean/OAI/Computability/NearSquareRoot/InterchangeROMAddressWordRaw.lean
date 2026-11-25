import OAI.Computability.NearSquareRoot.InterchangeROMAddressWord
import OAI.Computability.NearSquareRoot.InterchangeOpcodeCodec

/-! # Running the literal word accepted by the finite stage checker -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OpcodeProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Port
  IntegerMultiplication.Loom IntegerMultiplication.Adic IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims InterchangeROMAddress InterchangeAddress InterchangeSpace

/-- The executable word carries only numerical opcodes. Its certified output
permutation and its recursive-call price are those of the decoded legal word. -/
theorem run_raw : ∃ c : Clocks, ∀ {n b f : ℕ} [NeZero b] (P G S : Tape)
    (_ : solid P) (_ : solid G) (_ : solid S) (_ : 2 ≤ b) (l : ℕ)
    (ops : Opcode.Word) (ok : Opcode.admissible b n ops = true)
    (v : Keys P G S (Fin n) (Block b f) → Tree) (good : Tree → Prop) (_ : ∀ k, good (v k)),
    let ord := Equiv.refl (Fin n)
    let s := arrays ord (line b f) P G S
    let h := header f P G S
    let src := stripe s v
    let decoded := Opcode.decodeWord ops ok
    let dst := stripe s (v ∘ (recreation ord P G S f decoded (Opcode.legal_decodeWord ops ok)).symm)
    let tick := fun o => cost c b n o h s.count src src
    ∃ qs, qs.length = Opcode.price ops ∧
      (∀ q∈qs, Valid (b:=b) f s.count l P G S good q) ∧
      InterchangeROMSequence.Step (Request.job b) (word b n ops) (send h) src dst qs
        ((ops.map tick).sum+(ops.length+1)*(110*((send h).count+1)))
        (InterchangeBatch.dataSpace src.count (send h).count (childPeak tick ops))
        (InterchangeBatch.returnSpace (send h).count (childPeak tick ops)) := by
  obtain ⟨c,run⟩ := run_word
  refine ⟨c,?_⟩
  intro n b f nz P G S p g s hb l ops ok v good hgood
  let decoded := Opcode.decodeWord ops ok
  have enc : decoded.map Opcode.encode = ops := Opcode.encode_decodeWord ops ok
  have length := congrArg List.length enc
  simp only [List.length_map] at length
  let tick (o : Opcode.Op) := cost c b n o (header f P G S) (arrays (Equiv.refl (Fin n)) (line b f) P G S).count
    (stripe (arrays (Equiv.refl (Fin n)) (line b f) P G S) v) (stripe (arrays (Equiv.refl (Fin n)) (line b f) P G S) v)
  have peak (w : List (Lag (Fin n) b)) : childPeak (fun o => tick (Opcode.encode o)) w =
      childPeak tick (w.map Opcode.encode) := by
    induction w with
    | nil => rfl
    | cons m w ih => exact congrArg (max (tick (Opcode.encode m))) ih
  have mapped : decoded.map (fun o => tick (Opcode.encode o)) = ops.map tick := by
    rw [← enc,List.map_map]
    rfl
  have peak' := peak decoded
  rw [enc] at peak'
  obtain ⟨qs,card,typed,hstep⟩ := run P G S p g s hb l decoded (Opcode.legal_decodeWord ops ok) v good hgood
  refine ⟨qs,card.trans (Opcode.price_decodeWord ops ok),typed,?_⟩
  change InterchangeROMSequence.Step _ (word b n (decoded.map Opcode.encode)) _ _ _ qs
    ((decoded.map (fun o => tick (Opcode.encode o))).sum + (decoded.length+1)*_)
    (InterchangeBatch.dataSpace _ _ (childPeak (fun o => tick (Opcode.encode o)) decoded))
    (InterchangeBatch.returnSpace _ (childPeak (fun o => tick (Opcode.encode o)) decoded)) at hstep
  rwa [enc,mapped,length,peak'] at hstep

end OpcodeProgram

end NearSquareRoot
end Computability
end OAI
