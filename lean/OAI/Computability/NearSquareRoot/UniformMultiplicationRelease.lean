import OAI.Computability.NearSquareRoot.BoundedProgramCompile
import OAI.Computability.NearSquareRoot.BoundedReleaseClock
import OAI.Computability.NearSquareRoot.ScheduleSchoolIO
import OAI.Computability.IntegerMultiplication.Bits.Word

/-! # Compiling a space-bounded multiplication task to the manuscript's machine model

The input domain agrees definitionally with the earlier P192 multiplier's domain.
The same command loads all delimited inputs, executes the certified multiplication
task, decodes its result, and copies the raw product to a dedicated output tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication IntegerMultiplication.Code
open NearSquareRoot.Space

abbrev MultiplicationInput :=
  {p : {v : Interface.Pair // v.1.length = v.2.length} // 1 ≤ p.val.1.length}

namespace MultiplicationInput

abbrev operands (i : MultiplicationInput) : Interface.Pair := i.val.val
abbrev width (i : MultiplicationInput) : ℕ := i.operands.1.length

end MultiplicationInput

/-- An encoded multiplication command works on raw MSF operand lists as data,
before adding the delimiter loader and the full-width output scan. -/
abbrev MultiplicationTask (T : ℕ → ℕ) (S : ℕ) (z : MultiplicationInput → List Bool) :=
  BoundedTask (fun i => T i.width) (fun i => S * i.width)
    (fun i => send i.operands) (fun i => send (z i))

/-- Input/output and physical complexity of one machine, with prescribed resource bounds. -/
def PhysicalMultiplicationBound (T : ℕ → ℕ) (S : ℕ) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (bit : Bool → A) (sep blank : A) (inp out : I) (start : Q) (m : TM.Rule A Q I),
    Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧ sep ≠ blank ∧
    ∀ n : ℕ, 0 < n → ∀ x y : List Bool, x.length = n → y.length = n →
      let init := initialConfig start inp bit sep blank x y
      ∃ (t : ℕ) (finish : TM.Config A Q I) (z : List Bool),
        Trace (TM.advance m) init t finish ∧ TM.advance m finish = none ∧
        TM.whole blank (z.map bit) (finish.tape out) ∧
        z.length = 2 * n ∧ bitValue z = bitValue x * bitValue y ∧
        t ≤ T n ∧ VisitsAtMost m init t (S * n)

private theorem raw_height (s : List Ltr) (j : ℕ) : (Schoolbook.raw s j).length ≤ s.length := by
  by_cases hj : j = 0 <;> simp [Schoolbook.raw, hj]

/-- The entire run of a single closed fixed-tape program has clock
`K * (T n + n + 1)` and a uniform linear visited-cell bound. -/
theorem physicalMultiplication_of_boundedTask {T : ℕ → ℕ} {S : ℕ}
    {z : MultiplicationInput → List Bool} (task : MultiplicationTask T S z)
    (hz : ∀ i, (z i).length = 2 * i.width ∧
      bitValue (z i) = bitValue i.operands.1 * bitValue i.operands.2) :
    ∃ K D : ℕ, PhysicalMultiplicationBound (fun n => K * (T n + n + 1)) D := by
  classical
  obtain ⟨cmd,C,hcmd⟩ := task
  let program := Schoolbook.loadCmd.join (cmd.join Schoolbook.unloadCmd)
  obtain ⟨A,Q,I,fA,fQ,fI,sym,blank,inp,out,start,m,K,inject,hblank,_,release⟩ :=
    bounded_release program
  refine ⟨2*C+160, K*(4*(C*(S+1)+128)+5), A,Q,I,fA,fQ,fI,sym ∘ Ltr.bit,sym .sep,
    blank,inp,out,start,m,inject.comp (fun _ _ h => Ltr.bit.inj h),
    fun b => ⟨fun eq => Ltr.noConfusion (inject eq), hblank _⟩, hblank _, ?_⟩
  intro n hn x y hx hy
  let i : MultiplicationInput := ⟨⟨(x,y), hx.trans hy.symm⟩, hx ▸ hn⟩
  have ni : i.width = n := hx
  have hzlen : (z i).length = 2*n := (hz i).1.trans (by rw [ni])
  let src := x.map Ltr.bit ++ .sep :: y.map Ltr.bit
  let dst := (z i).map Ltr.bit
  let cap := C*(S*n+1) + 64*(n+1)
  have load := Schoolbook.load_run x y []
  have loadHeight j : (Schoolbook.raw src j).length + (17 + 11*(x.length+y.length)) ≤ cap := by
    apply (Nat.add_le_add_right (raw_height _ _) _).trans
    simp only [src, List.length_append, List.length_cons, List.length_map, hx, hy]
    unfold cap
    omega
  have loadDepth : 17 + 11*(x.length+y.length) + 1 ≤ cap := by
    unfold cap; rw [hx, hy]; omega
  have hload := BoundedRun.clock (depth := 17+11*(x.length+y.length)) load loadHeight le_rfl
  obtain ⟨u,hu,core⟩ := hcmd i [] (fun _ => []) 0 (by intro j; rfl)
  simp only [Nat.zero_add] at core
  change u ≤ C*(T i.width+1) at hu
  rw [ni] at hu
  rw [Schoolbook.letters_pile_empty, Schoolbook.letters_pile_empty] at core
  change BoundedRun (C*(S*i.width+1)) (C*(S*i.width+1)) [] cmd
    (Schoolbook.raw (send (x, y)).spell) u (Schoolbook.raw (send (z i)).spell) at core
  rw [ni] at core
  have hcore := core.mono (show C*(S*n+1) ≤ cap by unfold cap; omega) le_rfl
  have unload := Schoolbook.unload_run (z i) []
  have encodedLength : (send (z i)).spell.length = 4*n+1 := by
    rw [Tree.spell_length]
    change size _ = _
    rw [Bits.size_word, hzlen]
    omega
  have endHeight j : (Schoolbook.raw (send (z i)).spell j).length + (6+12*(z i).length) ≤ cap := by
    have h := raw_height (send (z i)).spell j
    rw [encodedLength] at h
    unfold cap; rw [hzlen]; omega
  have hunload := BoundedRun.clock (cap := cap) (depth := cap) unload endHeight
    (by unfold cap; rw [hzlen]; omega)
  have all := hload.join (hcore.join hunload (by unfold cap; omega)) loadDepth
  let ticks := 1 + (17+11*(x.length+y.length)) + 1 + (1+u+1+(6+12*(z i).length))
  obtain ⟨initial, finish, inLoad, otherLoad, run, halt, word, space⟩ :=
    release src (Schoolbook.raw dst) ticks cap cap all
  let init := initialConfig start inp (sym ∘ Ltr.bit) (sym .sep) blank x y
  have beginEq : (⟨start, initial⟩ : TM.Config A Q I) = init := by
    congr 1
    funext j
    by_cases hj : j = inp
    · subst j
      simpa [src, init, initialConfig, List.map_map, List.map_append] using inLoad
    · simpa [init, initialConfig, hj] using otherLoad j hj
  rw [beginEq] at run space
  have ht : (Schoolbook.raw dst 0).length = 2*n := by simp [dst, hzlen]
  refine ⟨_, finish, z i, run, halt, ?_, hzlen, (hz i).2, ?_, ?_⟩
  · simpa [dst, List.map_map] using word
  · rw [ht]
    dsimp only [ticks]
    rw [hx, hy, hzlen]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hu ⊢
    omega
  · obtain ⟨cells, hcard, cover⟩ := space
    refine ⟨cells, hcard.trans ?_, cover⟩
    have hsn : S*n+1 ≤ (S+1)*n := by rw [Nat.add_mul]; omega
    have capBound : cap ≤ (C*(S+1)+128)*n := by
      have hc := Nat.mul_le_mul_left C hsn
      unfold cap
      rw [Nat.add_mul, Nat.mul_assoc]
      omega
    rw [max_self, Nat.mul_assoc]
    exact Nat.mul_le_mul_left K (by rw [Nat.add_mul, Nat.mul_assoc]; omega)

/-- The same released machine inherits each nonnegative logarithmic exponent
proved for its structured program, with the multiplicative constant depending
on the exponent. -/
theorem physicalMultiplication_exponents_of_boundedTask {T : ℕ → ℕ} {S : ℕ}
    {z : MultiplicationInput → List Bool} (task : MultiplicationTask T S z)
    (hz : ∀ i, (z i).length = 2 * i.width ∧
      bitValue (z i) = bitValue i.operands.1 * bitValue i.operands.2) :
    ∃ K D : ℕ, PhysicalMultiplicationBound (fun n => K * (T n + n + 1)) D ∧
      ∀ ρ : ℝ, 0 ≤ ρ → ∀ C : ℝ, 0 < C →
        (∀ᶠ n in Filter.atTop, (T n : ℝ) ≤ C * n * logScale n ^ ρ) →
        ∃ C' : ℝ, 0 < C' ∧ ∀ᶠ n in Filter.atTop,
          ((K * (T n + n + 1) : ℕ) : ℝ) ≤ C' * n * logScale n ^ ρ := by
  obtain ⟨K, D, machine⟩ := physicalMultiplication_of_boundedTask task hz
  exact ⟨K, D, machine, fun _ hρ _ hC bound => affine_io_eventually hρ hC bound K⟩

/-- If the one encoded command has all positive excess exponents, the compiled
machine satisfies the independently specified uniform multiplication theorem. -/
theorem uniformMultiplication_of_boundedTask {T : ℕ → ℕ} {S : ℕ}
    {z : MultiplicationInput → List Bool} (task : MultiplicationTask T S z)
    (hz : ∀ i, (z i).length = 2*i.width ∧
      bitValue (z i) = bitValue i.operands.1 * bitValue i.operands.2)
    (time : AllEpsilonBounds T) : UniformMultiplicationSpec := by
  obtain ⟨K,D,A,Q,I,fA,fQ,fI,bit,sep,blank,inp,out,start,m,hbit,hsep,hblank,releases⟩ :=
    physicalMultiplication_of_boundedTask task hz
  exact ⟨A,Q,I,fA,fQ,fI,bit,sep,blank,inp,out,start,m,_,D,hbit,hsep,hblank,
    (allEpsilonBounds_iff_forall_pos _).mp (time.affine_io K), releases⟩

end NearSquareRoot
end Computability
end OAI
