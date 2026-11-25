import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeRouted
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeQualitative

/-! # Totality and the sharp clock for an externally selected physical program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Node
open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode KernelPass ComputableSyntax
open GeneratorSyntax CommonRegisters PhysicalWalshContext

/-- Every successful flat routing implementation yields a terminating raw
piece on all admitted inputs, with no cost requirement on the routing clocks.
The efficient routing estimates give the separate sharp bounds on exactly the
same emitted command. -/
theorem compileRoutedTotalFor {Z : Type} [Primcodable Z] (s : ℕ → Raw) (hs : Computable s)
    (good : ∀ j, (interpreted (s j)).Good (j+3) (2*(j+2)))
    (flat : Z × Raw → Op → Cmd) (eff : Effective ltr (Function.uncurry flat))
    (M : ℕ) (bounded : ∀ r op, Within M (flat r op)) :
    ∃ (cmd : Z × ℕ → Cmd) (R D : ℕ), Computable (Dispatch.dimensions ∘ s) ∧ Computable (rawPrecisionCutoff ∘ s) ∧
      Effective ltr cmd ∧ 0 < R ∧ 1 ≤ D ∧ (∀ j, Within R (cmd j)) ∧
      ∃ sel : (j : ℕ) → Dispatch.Selected (j+3) (2*(j+2)) (s j),
      (∀ (z : Z) (j : ℕ) (scan arena : PhysicalWalshNode.Shape → ℕ),
        let a := (Dispatch.dimensions (s j)).1
        let W := (Dispatch.dimensions (s j)).2
        let hw : 0 < W := by have := (sel j).wide; dsimp [W]; omega
        Dispatch.XorRuns (fun raw => flat (z,raw)) a W (s j).2 scan arena →
        ∃ t r, EffectiveBoundedTask.Runs (cmd (z,j)) t r
          (rawInput hw (sel j).plan) (rawOutput hw (sel j).plan)) ∧
      ∀ (j d : ℕ), D ≤ d →
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
  obtain ⟨emit,N,e,hdims,hcut,he,_,_,fit,sel,body⟩ := Dispatch.midpointWithFor s hs good flat eff M bounded
  obtain ⟨tag,R,f,hf,hR,_,out,equip,checked⟩ := compile
    (fun z : Z × ℕ => Dispatch.dimensions (s z.2)) (hdims.comp Computable.snd) emit he N fit
  refine ⟨fun j => entry.join (tag j),R,max f e,hdims,hcut,out,hR,hf.trans (le_max_left ..),equip,sel,?_,?_⟩
  · intro z j scan arena a W hw routes
    let D := max f e
    let V (t : PhysicalWalshNode.Shape) := max (max (scan t) (arena t)) (nodeArena a W D t)
    have caps {n : ℕ} (hn : n ≤ D) (t : PhysicalWalshNode.Shape) : allowance (a+1) n t ≤ V t :=
      (allowance_mono hn t).trans ((le_max_left ..).trans (le_max_right ..))
    have fit (t : PhysicalWalshNode.Shape) : routeArena (coords a W) PhysicalWalshNode.Shape.w
        (Header.wire (a+1)) t ≤ V t := (le_max_right ..).trans (le_max_right ..)
    have widened : Dispatch.XorRuns (fun raw => flat (z,raw)) a W (s j).2 V V := by
      intro op tag hi hj apart
      exact (routes op tag hi hj apart).mono (fun _ => (le_max_left ..).trans (le_max_left ..))
        (fun _ => (le_max_right ..).trans (le_max_left ..))
    have run := body z j V V (fun _ => le_rfl) (caps (le_max_right ..)) fit widened
    exact total_of_trace hw (sel j).plan V V (fun _ => le_rfl) (tag (z,j))
      (checked (z,j) hw (sel j).plan V V (fun _ => le_rfl) (caps (le_max_left ..)) run).1
  · intro j d hd a W p hw ρ
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

end PhysicalWalshCompile.Node

end NearSquareRoot
end Computability
end OAI
