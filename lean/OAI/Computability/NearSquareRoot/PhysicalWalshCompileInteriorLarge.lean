import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorEnds
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapPrefixCommand

/-! # Compiling the complete large canonical XOR on a real Walsh row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInterior

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode Interior SwapPrefix
open PhysicalWalshCompileXorRoute CommonRegisters GeneratorSyntax KernelPass.ComputableSyntax

/-- The compiler inserts the packing rulers and pads the row before the selected
native gate. Its file, register bound and descriptor degree work for every
admission predicate. The same file inherits both the sharp estimate and
termination with arbitrary input-dependent bounds. -/
theorem compileOnTotal {J : Type} [Primcodable J] (raw : J → Raw)
    (core : J → Cmd) (rawComp : Computable raw)
    (eff : Effective ltr core) (N : ℕ) (reg : ∀ j, Within N (core j)) :
    ∃ (emit : J → Cmd) (M d : ℕ), Effective ltr emit ∧ 1 ≤ d ∧
      (∀ j, Within M (emit j)) ∧ ∀ j a W ops (ha : 4 ≤ a),
      raw j = (a+1,ops) → (Packed.decode (a+1) ops).i = W →
      ∀ pred : PhysicalWalshNode.Shape → Prop,
        (∀ ρ : ℝ, NativeOn a W ρ pred (core j) → LargeOn ρ pred d a W ha (emit j)) ∧
        (NativeTotalOn a W pred (core j) → TotalOn a W ha pred (emit j)) := by
  obtain ⟨H,e,headers,he,epos,hr,hrun⟩ := PhysicalWalshCompileInteriorHeader.compiledRaw
  obtain ⟨P,_,pr⟩ := SwapPrefixCmd.within
  obtain ⟨K,R,kit⟩ := exists_kit
  let M := max (max N H) (max R P)
  let d := max e SwapPrefixCmd.degree
  have n : N ≤ M := (le_max_left ..).trans (le_max_left ..)
  have h : H ≤ M := (le_max_right ..).trans (le_max_left ..)
  have r : R ≤ M := (le_max_left ..).trans (le_max_right ..)
  have p : P ≤ M := (le_max_right ..).trans (le_max_right ..)
  let key j := dimensions (raw j)
  let head j := headers (0,raw j)
  let emit j := (SwapPrefixCmd.pre (key j)).join
    (K.chain ((head j).join (core j)) (SwapPrefixCmd.post (key j)))
  have dims : Computable key := computable_dimensions.comp rawComp
  have headEff : Effective ltr head := he.comp ((Computable.const 0).pair rawComp)
  have preEff : Effective ltr (fun j => SwapPrefixCmd.pre (key j)) := SwapPrefixCmd.effective_pre.comp dims
  refine ⟨emit,M,d,preEff.join
    (K.effective_chain (headEff.join eff) (SwapPrefixCmd.effective_post.comp dims)),
    epos.trans (le_max_left ..),fun j => ⟨RegisterSelect.within_mono p _ (pr _).1,
      kit.within_chain r ⟨RegisterSelect.within_mono h _ (hr _),RegisterSelect.within_mono n _ (reg _)⟩
      (RegisterSelect.within_mono p _ (pr _).2)⟩,?_⟩
  intro j a W ops ha eqn width pred
  let u (i : {t : XorInput W // pred t.shape}) := i.val.shape
  let x (i : {t : XorInput W // pred t.shape}) := i.val.row
  have decoded : key j = (a+1,W) := by rw [show key j=dimensions (raw j) from rfl,eqn,dimensions_eq a W ops width]
  have hd : 1 ≤ d := epos.trans (le_max_left ..)
  have pd i : allowance (a+1) SwapPrefixCmd.degree (u i) ≤ allowance (a+1) d (u i) :=
    allowance_mono (le_max_right ..) (u i)
  have ed i : allowance (a+1) e (u i) ≤ allowance (a+1) d (u i) :=
    allowance_mono (le_max_left ..) (u i)
  let row (i : {t : XorInput W // pred t.shape}) := send (padded (a:=a) i.val)
  have small : PhysicalWalshCompile.Small (allowance (a+1) e ∘ u) row := by
    refine ⟨17,fun i => ?_⟩
    have bound := stream_cost (a+1) W e (u i) _ (extend (a+1) W (u i) (x i)) le_rfl
    change size (stream (paddedSize (a+1) W (u i)) (extend (a+1) W (u i) (x i))) ≤ _
    change _ ≤ 17*(allowance (a+1) e (u i)+1)
    omega
  have prep := hrun a W ops width 0 ha _ u (fun i => i.val.positive) row small
  dsimp only [emit,head]
  rw [decoded,eqn]
  have pre := (SwapPrefixCmd.pre_runs (a+1) W u x).mono pd pd
  have headRun := prep.mono ed ed
  have post := (SwapPrefixCmd.post_runs (a+1) W u (fun i => moved (a:=a) i.val)).mono pd pd
  exact ⟨fun ρ coreRun => large_frame_on kit ha hd coreRun pre headRun post,
    fun total => large_frame_total kit ha total ⟨_,_,pre⟩ ⟨_,_,headRun⟩ ⟨_,_,post⟩⟩

/-- The sharp resource estimate for the emitted interior command. -/
theorem compileOn {J : Type} [Primcodable J] (raw : J → Raw)
    (core : J → Cmd) (rawComp : Computable raw)
    (eff : Effective ltr core) (N : ℕ) (reg : ∀ j, Within N (core j)) :
    ∃ (emit : J → Cmd) (M d : ℕ), Effective ltr emit ∧ 1 ≤ d ∧
      (∀ j, Within M (emit j)) ∧ ∀ j (ρ : ℝ) a W ops (ha : 4 ≤ a),
      raw j = (a+1,ops) → (Packed.decode (a+1) ops).i = W →
      ∀ pred : PhysicalWalshNode.Shape → Prop, NativeOn a W ρ pred (core j) →
        LargeOn ρ pred d a W ha (emit j) := by
  obtain ⟨emit,M,d,he,hd,hr,run⟩ := compileOnTotal raw core rawComp eff N reg
  exact ⟨emit,M,d,he,hd,hr,fun j ρ a W ops ha eqn width pred => (run j a W ops ha eqn width pred).1 ρ⟩

/-- A native exponent and reserve may vary arbitrarily across successful
templates. Its degree is needed for the execution theorem alone. -/
theorem compile_large {J : Type} [Primcodable J] (raw : J → Raw) (reserve : J → ℕ)
    (core : J → Cmd) (rawComp : Computable raw) (eff : Effective ltr core) (N : ℕ)
    (reg : ∀ j, Within N (core j)) :
    ∃ (emit : J → Cmd) (M d : ℕ), Effective ltr emit ∧ 1 ≤ d ∧
      (∀ j, Within M (emit j)) ∧ ∀ j (ρ : ℝ), Native ρ (reserve j) (core j) →
      ∀ a W ops (ha : 4 ≤ a), raw j = (a+1,ops) → (Packed.decode (a+1) ops).i = W →
        LargeRun ρ (reserve j) d a W ha (emit j) := by
  obtain ⟨emit,M,d,hc,hd,hr,run⟩ := compileOn raw core rawComp eff N reg
  exact ⟨emit,M,d,hc,hd,hr,fun j ρ native a W ops ha eqn width =>
    run j ρ a W ops ha eqn width _ (native a W ha)⟩

/-- At a fixed exponent the complete compiler accepts every raw template.
Its native program is the same for every arity and square bank width. -/
theorem fixed_large {ρ : ℝ} (lower : 1/2 < ρ) (upper : ρ ≤ 1) :
    ∃ (D d M : ℕ) (emit : Raw → Cmd), Effective ltr emit ∧ 1 ≤ d ∧
      (∀ raw, Within M (emit raw)) ∧ ∀ a W ops (ha : 4 ≤ a), (Packed.decode (a+1) ops).i = W →
        LargeRun ρ D d a W ha (emit (a+1,ops)) := by
  obtain ⟨D,c,cc⟩ := exists_native lower upper
  obtain ⟨N,hN⟩ := (RegisterSelect.within_eventually c).exists
  obtain ⟨emit,M,d,he,hd,hr,run⟩ := compile_large (J:=Raw) id (fun _ => D) (fun _ => c)
    Computable.id (effective_const _ _) N (fun _ => hN)
  exact ⟨D,d,M,emit,he,hd,hr,fun a W ops ha width => run (a+1,ops) ρ cc a W ops ha rfl width⟩

end PhysicalWalshCompileInterior

end NearSquareRoot
end Computability
end OAI
