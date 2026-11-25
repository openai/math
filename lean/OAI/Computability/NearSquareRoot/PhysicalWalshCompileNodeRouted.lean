import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNode
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeRate
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSelected

/-! # Effective generation and resource bounds of the selected recursive Walsh pieces -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Node

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode KernelPass ComputableSyntax
open GeneratorSyntax CommonRegisters PhysicalWalshContext

/-- All selected exponents use one effective command family and a common
register bank. The independent time and peak-space estimates apply to each
generated command on the actual flat record packets. -/
theorem compileRoutedWith {Z : Type} [Primcodable Z] (flat : Z × Raw → Op → Cmd) (eff : Effective ltr (Function.uncurry flat))
    (M : ℕ) (bounded : ∀ r op, Within M (flat r op)) :
    ∃ (s : ℕ → Raw) (cmd : Z × ℕ → Cmd) (R D : ℕ), Computable s ∧
      Computable (Dispatch.dimensions ∘ s) ∧ Computable (rawPrecisionCutoff ∘ s) ∧
      Effective ltr cmd ∧ 0 < R ∧ 1 ≤ D ∧ (∀ j, Within R (cmd j)) ∧
      ∃ sel : (j : ℕ) → Dispatch.Selected (j+3) (2*(j+2)) (s j), ∀ (j d : ℕ), D ≤ d →
        let a := (Dispatch.dimensions (s j)).1
        let W := (Dispatch.dimensions (s j)).2
        let p := (sel j).plan
        let hw : 0 < W := by have := (sel j).wide; dsimp [W]; omega
        let ρ := ((j+3 : ℕ) : ℝ)/(2*(j+2) : ℕ)
        ∃ K : ℕ, 1 ≤ K ∧ ∀ (z : Z) (extra : PhysicalWalshNode.Shape → ℕ),
          Dispatch.XorRuns (fun raw => flat (z,raw)) a W (s j).2 (nodeScan a W d extra) (nodeArena a W d) →
          ∀ (c : ℝ) (L P : ℕ → ℝ), 0 ≤ c → (∀ w, 1 ≤ L w) → (∀ w, 0 ≤ P w) →
          (∀ t, withinWidth (a+1) t → (extra t : ℝ) ≤ localTime (a+1) ρ c (L t.w) (P t.w) t.level
            (bitVolume (a+1) t)) →
          ∃ B : ℝ, 0 ≤ B ∧ EffectiveBoundedTask.Runs (cmd (z,j))
            (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls ρ B L (envelopeSetup K d P) v.val.shape)
            (fun v => pieceSpaceBound (a+1) (4*K+c) (envelopeSetup K d P) v.val.shape)
            (rawInput hw p) (rawOutput hw p) := by
  obtain ⟨s,emit,N,e,hs,hdims,hcut,he,_,_,fit,sel,body⟩ := Dispatch.midpointWith flat eff M bounded
  obtain ⟨tag,R,f,hf,hR,_,out,equip,checked⟩ := compile
    (fun z : Z × ℕ => Dispatch.dimensions (s z.2)) (hdims.comp Computable.snd) emit he N fit
  refine ⟨s,fun j => entry.join (tag j),R,max f e,hs,hdims,hcut,out,hR,hf.trans (le_max_left ..),equip,sel,?_⟩
  intro j d hd a W p hw ρ
  have hf' : f ≤ d := (le_max_left ..).trans hd
  have he' : e ≤ d := (le_max_right ..).trans hd
  have positive : 2 ≤ a+1 := (by decide : 2 ≤ 5).trans (sel j).large
  have hr : 0 ≤ ρ := by dsimp [ρ]; positivity
  obtain ⟨K,hK,rate⟩ := routedNamedPieceRate hw p d (hf.trans hf') positive (sel j).wide hr (sel j).saving
  refine ⟨K,hK,fun z extra routes => ?_⟩
  let scan := nodeScan a W d extra
  let arena := nodeArena a W d
  have cost (t) : arena t ≤ scan t := Nat.le_add_right ..
  have capacity (n : ℕ) (h : n ≤ d) (t : PhysicalWalshNode.Shape) : allowance (a+1) n t ≤ arena t :=
    (allowance_mono h t).trans (le_max_left ..)
  have run := body z j scan arena cost (capacity e he') (fun _ => le_max_right ..) routes
  exact rate extra (tag (z,j)) (checked (z,j) hw p scan arena cost (capacity f hf') run).2

/-- The midpoint selector and raw program files with no extra compilation parameter. -/
theorem compileRouted (flat : Raw → Op → Cmd) (eff : Effective ltr (Function.uncurry flat))
    (M : ℕ) (bounded : ∀ r op, Within M (flat r op)) :
    ∃ (s : ℕ → Raw) (cmd : ℕ → Cmd) (R D : ℕ), Computable s ∧
      Computable (Dispatch.dimensions ∘ s) ∧ Computable (rawPrecisionCutoff ∘ s) ∧
      Effective ltr cmd ∧ 0 < R ∧ 1 ≤ D ∧ (∀ j, Within R (cmd j)) ∧
      ∃ sel : (j : ℕ) → Dispatch.Selected (j+3) (2*(j+2)) (s j), ∀ (j d : ℕ), D ≤ d →
        let a := (Dispatch.dimensions (s j)).1
        let W := (Dispatch.dimensions (s j)).2
        let p := (sel j).plan
        let hw : 0 < W := by have := (sel j).wide; dsimp [W]; omega
        let ρ := ((j+3 : ℕ) : ℝ)/(2*(j+2) : ℕ)
        ∃ K : ℕ, 1 ≤ K ∧ ∀ extra : PhysicalWalshNode.Shape → ℕ,
          Dispatch.XorRuns flat a W (s j).2 (nodeScan a W d extra) (nodeArena a W d) →
          ∀ (c : ℝ) (L P : ℕ → ℝ), 0 ≤ c → (∀ w, 1 ≤ L w) → (∀ w, 0 ≤ P w) →
          (∀ t, withinWidth (a+1) t → (extra t : ℝ) ≤ localTime (a+1) ρ c (L t.w) (P t.w) t.level
            (bitVolume (a+1) t)) →
          ∃ B : ℝ, 0 ≤ B ∧ EffectiveBoundedTask.Runs (cmd j)
            (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls ρ B L (envelopeSetup K d P) v.val.shape)
            (fun v => pieceSpaceBound (a+1) (4*K+c) (envelopeSetup K d P) v.val.shape)
            (rawInput hw p) (rawOutput hw p) := by
  obtain ⟨s,emit,N,e,hs,hdims,hcut,he,_,_,fit,sel,body⟩ := Dispatch.midpoint flat eff M bounded
  obtain ⟨tag,R,f,hf,hR,_,out,equip,checked⟩ := compile (Dispatch.dimensions ∘ s) hdims emit he N fit
  refine ⟨s,fun j => entry.join (tag j),R,max f e,hs,hdims,hcut,out,hR,hf.trans (le_max_left ..),equip,sel,?_⟩
  intro j d hd a W p hw ρ
  have hf' : f ≤ d := (le_max_left ..).trans hd
  have he' : e ≤ d := (le_max_right ..).trans hd
  have positive : 2 ≤ a+1 := (by decide : 2 ≤ 5).trans (sel j).large
  have hr : 0 ≤ ρ := by dsimp [ρ]; positivity
  obtain ⟨K,hK,rate⟩ := routedNamedPieceRate hw p d (hf.trans hf') positive (sel j).wide hr (sel j).saving
  refine ⟨K,hK,fun extra routes => ?_⟩
  let scan := nodeScan a W d extra
  let arena := nodeArena a W d
  have cost (t) : arena t ≤ scan t := Nat.le_add_right ..
  have capacity (n : ℕ) (h : n ≤ d) (t : PhysicalWalshNode.Shape) : allowance (a+1) n t ≤ arena t :=
    (allowance_mono h t).trans (le_max_left ..)
  have run := body j scan arena cost (capacity e he') (fun _ => le_max_right ..) routes
  exact rate extra (tag j) (checked j hw p scan arena cost (capacity f hf') run).2

end PhysicalWalshCompile.Node

end NearSquareRoot
end Computability
end OAI
