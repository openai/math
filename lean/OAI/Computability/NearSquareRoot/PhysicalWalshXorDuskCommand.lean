import OAI.Computability.NearSquareRoot.PhysicalWalshXorCodecCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshXorFrameCommand

/-! # Compiling a named packed XOR into the physical Dusk record command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication Code Strip Space EffectiveBoundedTask CommonRegisters GeneratorSyntax Filter
open Controlled.PositionProgram XorSweep
noncomputable section

/-- Both codecs and all physical packet rearrangements have fixed source
files. Only the native XOR core varies with the generated candidate. -/
def duskCmd (gate : Cmd) := threeCmd packCmd gate unpackCmd

theorem duskCmd_effective {P : Type} [Primcodable P] {c : P → Cmd}
    (h : Effective ltr c) : Effective ltr (fun p => duskCmd (c p)) :=
  threeCmd_effective (effective_const _ _) h (effective_const _ _)

theorem duskCmd_within (R : ℕ) : ∃ K, 0 < K ∧ ∀ c, Within R c → Within K (duskCmd c) := by
  obtain ⟨B,_,wrap⟩ := threeCmd_within
  obtain ⟨K,h,p,u⟩ := ((eventually_gt_atTop (max R B)).and
    ((RegisterSelect.within_eventually packCmd).and (RegisterSelect.within_eventually unpackCmd))).exists
  refine ⟨K,by omega,fun c hc => wrap K (by omega) _ _ _ p (RegisterSelect.within_mono (by omega) _ hc) u⟩

/-- The generated command acts on the raw ordered words, with time and
workspace inherited from the named core provided that it can scan its input. -/
theorem duskOfGateNamed {I : Type} (P L S w : I → ℕ) (hs : ∀ i, 0 < S i)
    (h : I → Tree) (time space : I → ℕ) (dom : ∀ i, space i ≤ time i)
    (x : (i:I) → ℕ → Dusk.Grain (w i))
    (io : ∀ i, (2^(P i+3*L i)*S i+1)*(w i+1) ≤ space i)
    {c : Cmd}
    (inner : EffectiveBoundedTask.Runs c time space
      (fun i => .fork (h i) (store (Series.natural (S i*(2*(w i+1)))) (duskRow (P:=P i) (L:=L i) (x i))))
      (fun i => store (Series.natural (S i*(2*(w i+1))))
        (duskRow (P:=P i) (L:=L i) (x i) ∘ directed (gate (L i))))) :
    EffectiveBoundedTask.Runs (duskCmd c) time space
      (fun i => .fork (duskHeader (h i) (2^(P i+3*L i)) (S i) (w i))
        (send ((List.range (2^(P i+3*L i)*S i)).map (Dusk.mark ∘ x i))))
      (fun i => send ((List.range (2^(P i+3*L i)*S i)).map
        (Dusk.mark ∘ x i ∘ directedRead (L i) (S i)))) := by
  let n i := 2^(P i+3*L i)
  let y i := x i ∘ directedRead (L i) (S i)
  have pk := (packRuns n S w x (fun _ => Nat.two_pow_pos _) hs).mono io io
  have un := (unpackRuns n S w y (fun _ => Nat.two_pow_pos _) hs).mono io io
  apply threeKeysNamed dom pk _ un
  simpa only [store_row,store_result (hs _)] using inner

end
end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
