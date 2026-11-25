import OAI.Computability.NearSquareRoot.PhysicalWalshCompileEffective
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSound
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileRegisters
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank
import OAI.Computability.NearSquareRoot.KernelUniformBinaryTemplate

/-! # Compiling the selected family to effective, register-bounded commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code PhysicalWalsh KernelPass KernelPass.ComputableSyntax
open GeneratorSyntax CommonRegisters

/-- An effective fixed-register emitter for the four primitive instructions
extends to an effective fixed-register family of complete physical templates.
Every output command is verified on the particular rows that reach it. -/
theorem compile_family {X : Type} [Primcodable X] (H R : Type) [Codec H] [Codec R]
    (raw : X → Raw) (hr : Computable raw) (leaf : X → Op → Cmd)
    (he : Effective ltr (Function.uncurry leaf)) (L : ℕ) (hl : ∀ x op, Within L (leaf x op)) :
    ∃ (c : X → Cmd) (N : ℕ), Effective ltr c ∧ 0 < N ∧ (∀ x, Within N (c x)) ∧
      ∀ x (I U : Type) (l : Layout U H R) (m : Meter U) (u : I → U)
        (f : Ops (raw x).1 l) (G : Guards (raw x).1 l), FitsLayout m l →
        (∀ op, Implements f G m u (Packed.leaf (raw x).1 op) (leaf x op)) →
        Implements f G m u (Packed.decode (raw x).1 (raw x).2) (c x) := by
  obtain ⟨b,ok,hs,n,hn,hcut,hswap,hfinish⟩ := effectiveBankRegisters H R
  let c x := command b .pass (fun _ => leaf x) (raw x).1 (raw x).2
  let N := max n L
  have nN : n ≤ N := le_max_left ..
  have lN : L ≤ N := le_max_right ..
  refine ⟨c,N,effective_family b .pass leaf _ _ (Computable.fst.comp hr) (Computable.snd.comp hr) hs he,
    hn.trans_le nN,fun x => ?_,?_⟩
  · exact command_within (hn.trans_le nN) b .pass (fun _ => leaf x)
      (fun i => RegisterSelect.within_mono nN _ (hcut i)) (RegisterSelect.within_mono nN _ hswap)
      (RegisterSelect.within_mono nN _ hfinish) trivial (fun _ op => RegisterSelect.within_mono lN _ (hl x op)) _ _
  · intro x I U l m u f G fit leaves
    exact command_sound f G u fit b ok .pass (fun _ => leaf x) (empty_sound f G u fit) leaves _

/-- A computable, strictly saving selector supplies the exact grammar consumed
by the compiler. The leaf programs may depend on the entire selected record. -/
theorem compile_midpoint (H R : Type) [Codec H] [Codec R] (leaf : Raw → Op → Cmd)
    (he : Effective ltr (Function.uncurry leaf)) (L : ℕ) (hl : ∀ x op, Within L (leaf x op)) :
    ∃ (s : ℕ → Raw) (c : ℕ → Cmd) (N : ℕ), Computable s ∧ Effective ltr c ∧ 0 < N ∧
      (∀ j, (interpreted (s j)).Good (j+3) (2*(j+2)) ∧ Within N (c j)) ∧
      ∀ j (I U : Type) (l : Layout U H R) (m : Meter U) (u : I → U)
        (f : Ops (s j).1 l) (G : Guards (s j).1 l), FitsLayout m l →
        (∀ op, Implements f G m u (Packed.leaf (s j).1 op) (leaf (s j) op)) →
        Implements f G m u (Packed.decode (s j).1 (s j).2) (c j) := by
  obtain ⟨s,hs,hgood⟩ := computable_midpoint_templates
  obtain ⟨c,N,ec,hN,reg,sound⟩ := compile_family H R s hs (fun j => leaf (s j))
    (he.comp ((hs.comp Computable.fst).pair Computable.snd)) L (fun j => hl (s j))
  exact ⟨s,c,N,hs,ec,hN,fun j => ⟨hgood j,reg j⟩,sound⟩

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
