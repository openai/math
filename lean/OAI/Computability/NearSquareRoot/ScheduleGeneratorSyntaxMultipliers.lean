import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxMultiplication

/-! # A fixed physical multiplier for a computably generated family of certified bodies -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet
open IntegerMultiplication.Code (Cmd Ltr)

/-- The same finite tapes and rule compute full-width products at every candidate
index. The time and space coefficients may depend on that index. -/
theorem unary_multipliers {R M : ℕ} (hR : 0 < R) (p : ℕ → Cmd) (eff : Effective ltr p)
    (bound : ∀ j, CommonRegisters.Within R (p j)) (T : ℕ → ℕ → ℕ) (S C : ℕ → ℕ)
    (z : ℕ → MultiplicationInput → List Bool)
    (body : ∀ j, MultiplicationBody (p j) (T j) (S j) (C j) (z j))
    (product : ∀ j i, (z j i).length = 2*i.width ∧
      bitValue (z j i) = bitValue i.operands.1 * bitValue i.operands.2)
    (mark : Universal.Letter Public.Letter (Pipeline.Index (Option (FixedTapes R))))
    (distinct : Sum.inl none ≠ mark)
    (enum : Universal.Tag Public.Letter (Pipeline.Index (Option (FixedTapes R))) ≃ Fin (M+1)) :
    ∃ g : Turing.ToPartrec.Code, Finite (GeneratorInputRun.Control g M) ∧
      Finite (GeneratorInputRun.Index (Pipeline.Index (Option (FixedTapes R)))) ∧
      ∀ j, ∃ K D : ℕ, ∀ (H : ℤ) (i : MultiplicationInput),
        let m := GeneratorInputRun.rule none mark g enum
        let init := GeneratorInputRun.initial none mark g H j (Pipeline.publicLoad i.operands.1 i.operands.2)
        ∃ t done, t ≤ K*(T j i.width+i.width+1) ∧ Trace (TM.advance m) init t done ∧
          TM.advance m done = none ∧ done.tape (.inl ()) = Generator.Input.source (.inl none) mark H j ∧
          done.tape (.inr (.inr (.inl (.inl true)))) =
            TM.Tape.loaded (.inl none) ((z j i).map fun b => .inl (Public.bit b)) ∧
          (z j i).length = 2*i.width ∧ bitValue (z j i) = bitValue i.operands.1 * bitValue i.operands.2 ∧
          VisitsAtMost m init t (D*i.width) := by
  obtain ⟨g,hg,hi,work⟩ := unary_family hR (fun j => multiplyWrap (p j))
    (effective_multiplyWrap eff) (fun j => within_multiplyWrap hR (bound j)) mark distinct enum
  refine ⟨g,hg,hi,fun j => ?_⟩
  obtain ⟨E,_,run⟩ := work j
  let d := C j * (S j + 1) + 128
  refine ⟨E*(2*(C j+46)+8), E*((R+2)*(4*d+6)+5),fun H i => ?_⟩
  obtain ⟨len,prod⟩ := product j i
  obtain ⟨n,nt,exec⟩ := multiplyWrap_run (body j) i len
  obtain ⟨t,done,time,tr,halt,restored,out,cells⟩ := run H i.operands.1 i.operands.2 (z j i) exec rfl
  have hwidth : i.operands.2.length = i.width := i.val.property.symm
  have positive : 1 ≤ i.width := i.property
  refine ⟨t,done,time.trans ?_,tr,halt,restored,out,len,prod,?_⟩
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [len,hwidth]
    change 2*n+1+2*i.width+i.width+i.width+2*i.width+1 ≤ _
    nlinarith only [nt, Nat.zero_le (T j i.width)]
  · obtain ⟨F,card,seen⟩ := cells
    refine ⟨F,card.trans ?_,seen⟩
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    simp only [max_self,len,hwidth]
    change (R+2)*(4*(d*i.width)+6)+i.width+i.width+2*i.width+1 ≤ _
    have h := Nat.mul_le_mul_left (R+2) (show 4*(d*i.width)+6 ≤ (4*d+6)*i.width by
      calc
        4*(d*i.width)+6 ≤ 4*(d*i.width)+6*i.width :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right _ positive) _
        _ = (4*d+6)*i.width := by ring)
    calc
      _ ≤ (R+2)*((4*d+6)*i.width)+5*i.width := by omega
      _ = _ := by ring

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
