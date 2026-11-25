import OAI.Computability.NearSquareRoot.PhysicalWalshXorFrames
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Generated command for packing, permuting, and unpacking a Walsh row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code CommonRegisters KernelEffectiveFamily GeneratorSyntax Filter

/-- The first two calls preserve the unread keys in the right child.
The last call consumes the unpacking key. -/
noncomputable def threeCmd (first middle last : Cmd) : Cmd :=
  ((((framePackCmd.join (leftCmd first)).join frameGateCmd).join
    (leftCmd middle)).join frameUnpackCmd).join last

theorem threeCmd_effective {P : Type} [Primcodable P] {f g h : P → Cmd}
    (hf : Effective ltr f) (hg : Effective ltr g) (hh : Effective ltr h) :
    Effective ltr (fun p => threeCmd (f p) (g p) (h p)) :=
  (((((effective_const ltr framePackCmd).join (effective_left hf)).join
    (effective_const ltr frameGateCmd)).join (effective_left hg)).join
    (effective_const ltr frameUnpackCmd)).join hh

/-- The three fixed key rearrangements need a constant number of registers
independent of all three emitted subcommands. -/
theorem threeCmd_within : ∃ B : ℕ, 0 < B ∧ ∀ R, B ≤ R → ∀ f g h : Cmd,
    Within R f → Within R g → Within R h → Within R (threeCmd f g h) := by
  obtain ⟨B,three,pack,gate,unpack⟩ := ((eventually_ge_atTop 3).and
    ((RegisterSelect.within_eventually framePackCmd).and
      ((RegisterSelect.within_eventually frameGateCmd).and (RegisterSelect.within_eventually frameUnpackCmd)))).exists
  refine ⟨B,by omega,fun R le f g h hf hg hh => ?_⟩
  have enough : 1 ≤ R := by omega
  exact ⟨⟨⟨⟨⟨RegisterSelect.within_mono le _ pack,within_left enough hf⟩,RegisterSelect.within_mono le _ gate⟩,
    within_left enough hg⟩,RegisterSelect.within_mono le _ unpack⟩,hh⟩

/-- Run exactly the three supplied files in one arena. Only the middle call
may exceed the linear scan time. -/
theorem threeKeysNamed {I : Type} {time space : I → ℕ} (fits : ∀ i, space i ≤ time i)
    {a h b p x y q : I → Tree} {c d e : Cmd}
    (first : EffectiveBoundedTask.Runs c space space (fun i => .fork (a i) (p i)) x)
    (middle : EffectiveBoundedTask.Runs d time space (fun i => .fork (h i) (x i)) y)
    (last : EffectiveBoundedTask.Runs e space space (fun i => .fork (b i) (y i)) q) :
    EffectiveBoundedTask.Runs (threeCmd c d e) time space
      (fun i => .fork (.fork (a i) (.fork (h i) (b i))) (p i)) q :=
  command_contract (threeCmd c d e) from threeKeys fits first.task middle.task last.task

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
