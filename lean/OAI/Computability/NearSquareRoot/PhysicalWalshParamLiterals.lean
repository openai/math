import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank

/-! # Specializing a physical Walsh command to two fixed parameters

The emitted prefix pushes the unary base and branching factor in register
zero and pairs them with the untouched run-time input. The cost constant
may depend on those two literals. All parameter choices use the same register
names as the joint interpreter together with register zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.ParamLiterals

open IntegerMultiplication Code CommonRegisters GeneratorSyntax EffectiveBoundedTask

def literal (A W : ℕ) : Tree := send (tally A,tally W)

def command (A W : ℕ) (core : Cmd) : Cmd :=
  PhysicalWalshCompile.withLiteral (literal A W) core

theorem effective (core : Cmd) : Effective ltr (fun p : ℕ×ℕ => command p.1 p.2 core) := by
  have a : Effective ltr (fun p : ℕ×ℕ => Task.prepare 0 (send (tally p.1))) := PhysicalWalshCompile.effective_tally_prepare.comp (Computable.fst (α := ℕ) (β := ℕ))
  have w : Effective ltr (fun p : ℕ×ℕ => Task.prepare 0 (send (tally p.2))) := PhysicalWalshCompile.effective_tally_prepare.comp (Computable.snd (α := ℕ) (β := ℕ))
  have fork := w.join (a.join (effective_const ltr (pack 0)))
  exact (fork.join (effective_const ltr (pack 0))).join (effective_const ltr core)

theorem within {R : ℕ} {core : Cmd} (Rpos : 0 < R) (h : Within R core) (A W : ℕ) :
    Within R (command A W core) :=
  ⟨⟨(RegisterWitness.prepare_within _).mpr Rpos,Rpos⟩,h⟩

theorem runs {I : Type} (A W : ℕ) {core : Cmd} {t s : I → ℕ} {u v : I → Tree}
    (h : EffectiveBoundedTask.Runs core t s (fun i => .fork (literal A W) (u i)) v)
    (input : ∀ i, (u i).count ≤ s i) : EffectiveBoundedTask.Runs (command A W core) t s u v := by
  let c := (Task.prepare 0 (literal A W)).join (pack 0)
  have prefixRun : EffectiveBoundedTask.Runs c (fun _ : I => 0) (fun i => (u i).count+0)
      u (fun i => .fork (literal A W) (u i)) := by
    apply EffectiveBoundedTask.Runs.of_time
    refine ⟨5*(literal A W).count+3,fun i env deck => ?_⟩
    simpa only [Nat.zero_add,Nat.mul_one] using
      (Task.fits_prepare 0 (literal A W) env (pile 0 (u i) deck)).join
        (fits_pack (literal A W) (u i) deck 0 env)
  exact (prefixRun.mono (fun _ => Nat.zero_le _) (fun i => by simpa using input i)).sequence h

end PhysicalWalsh.ParamLiterals

end NearSquareRoot
end Computability
end OAI
