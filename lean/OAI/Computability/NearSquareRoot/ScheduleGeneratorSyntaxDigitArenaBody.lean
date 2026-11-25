import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxMultiplication

/-! # Multiplication bodies with a width-dependent space allowance -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication IntegerMultiplication.Code Space

/-- The command is fixed while the allowed space and running time may each
depend on the common operand length. -/
def ArenaBody (p : Cmd) (T S : ℕ → ℕ) (C : ℕ) (z : MultiplicationInput → List Bool) : Prop :=
  ∀ i env r base, (∀ j, (letters r j).length ≤ base) →
    BoundedFits env p (pile 0 (send i.operands) r) (pile 0 (send (z i)) r)
      (C*(T i.width+1)) (base+C*(S i.width+1)) (C*(S i.width+1))

theorem multiplyWrap_arena_run {p : Cmd} {T S : ℕ → ℕ} {C : ℕ} {z : MultiplicationInput → List Bool}
    (body : ArenaBody p T S C z) (i : MultiplicationInput) (length : (z i).length = 2*i.width) :
    let n := i.width
    let cap := (C+64)*(S n+n+1)
    ∃ t ≤ (C+46)*(T n+n+1), BoundedRun cap cap [] (multiplyWrap p)
      (Schoolbook.raw (rawPair i.operands.1 i.operands.2)) t (Schoolbook.raw ((z i).map Ltr.bit)) := by
  have run := body i [] (fun _ => []) 0 (by intro j; rfl)
  simp only [Nat.zero_add] at run
  obtain ⟨t,time,h⟩ := multiplyWrap_at i (z i) length run
  have space : C*(S i.width+1)+64*(i.width+1) ≤ (C+64)*(S i.width+i.width+1) := by
    have ha := Nat.mul_le_mul_left C (show S i.width+1 ≤ S i.width+i.width+1 by omega)
    have hb := Nat.mul_le_mul_left 64 (show i.width+1 ≤ S i.width+i.width+1 by omega)
    rw [Nat.add_mul]
    exact Nat.add_le_add ha hb
  exact ⟨t,time,h.mono space space⟩

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
