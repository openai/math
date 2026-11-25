import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorRouteParam
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryGraded
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquare
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileDispatchPlans

/-! # Named XOR routes at the square-logarithmic cutoff -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshEffectiveRoutes
open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode PhysicalWalshNode.FrontDispatch
open CommonRegisters GeneratorSyntax KernelPass.ComputableSyntax
open PhysicalWalshCompileXorRoute (Flat SwapArgs)
open PhysicalWalshCompileElementaryRelease (gradedCut)
open PhysicalWalshCompile (Dispatch.XorRuns)

noncomputable def extra (a W : ℕ) (ρ : ℝ) (s : PhysicalWalshNode.Shape) :=
  ElementarySweep.prefixExtra (a+1) (gradedCut (a+1)) s + SlotSwap.wideExtra ρ (a+1) s + squareExtra a W ρ s

/-- Every generated call uses the same arena. The prefix, high rectangle,
and front gate can each use the full routed time allowance. -/
theorem extra_bound {a W : ℕ} (arity : 2 ≤ a+1) {ρ : ℝ} (half : 1/2 ≤ ρ) (upper : ρ ≤ 1)
    (s : PhysicalWalshNode.Shape) (admit : withinWidth (a+1) s) :
    (extra a W ρ s : ℝ) ≤ localTime (a+1) ρ (74*(4+(2:ℝ)^ρ+5505)) (RouterClock.logWidth s.w) 0
      s.level (bitVolume (a+1) s) := by
  have cut : gradedCut (a+1) = fun t => min (ElementarySchedule.slotWidth (a+1) t)
      ((Nat.clog 2 (Header.scale (a+1) t+1))^2) := funext (fun _ => by simp [gradedCut,SlotSwap.reserve,Controlled.payloadBits,pow_two])
  rw [extra,cut]
  exact XorSquare.combined_clock arity half (B:=5505) (by norm_num)
      (fun t _ => squareExtra_bound a W half upper t) s admit

variable {Z : Type} [Primcodable Z]

def Upper (high : Z × SwapArgs → Cmd) (z : Z) (a W : ℕ) (ops : List Op) (d : ℕ) (ρ : ℝ) :=
  ∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W)
    (nodeScan a W d (SlotSwap.wideExtra ρ (a+1))) (nodeArena a W d) (Route.upperSwap (gradedCut (a+1)) i j)
    (high (z,(a+1,ops),i.val,j.val))

def Front (front : Z × Raw → Cmd) (z : Z) (a W : ℕ) (ops : List Op) (d : ℕ) (ρ : ℝ) (arity : 4 ≤ a) :=
  PhysicalWalshCompileXorPacket.FlatRuns (W:=W) (nodeScan a W d (squareExtra a W ρ)) (nodeArena a W d)
    (Interior.axes a arity) (front (z,a+1,ops))

def UpperAt (high : Z × SwapArgs → Cmd) (z : Z) (a W : ℕ) (ops : List Op)
    (scan arena : PhysicalWalshNode.Shape → ℕ) :=
  ∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W) scan arena (Route.upperSwap (gradedCut (a+1)) i j)
    (high (z,(a+1,ops),i.val,j.val))

def FrontAt (front : Z × Raw → Cmd) (z : Z) (a W : ℕ) (ops : List Op)
    (scan arena : PhysicalWalshNode.Shape → ℕ) (arity : 4 ≤ a) :=
  PhysicalWalshCompileXorPacket.FlatRuns (W:=W) scan arena (Interior.axes a arity) (front (z,a+1,ops))

/-- Three generated low-field XOR passes and a generated high rectangle
perform one whole-slot transposition. The five-pass compiler requests
strictly ordered axes. -/
private theorem swaps (high : Z × SwapArgs → Cmd) (eh : Effective ltr high) (H : ℕ)
    (rh : ∀ k, Within H (high k)) :
    ∃ (swap : Z × SwapArgs → Cmd) (N E : ℕ), Effective ltr swap ∧ (∀ k, Within N (swap k)) ∧
      ∀ z a W ops d, E ≤ d → (Packed.decode (a+1) ops).i = W → ∀ scan arena,
        (∀ s, nodeArena a W d s ≤ arena s) → (∀ s, arena s ≤ scan s) →
        (∀ s, nodeScan a W d (ElementarySweep.prefixExtra (a+1) (gradedCut (a+1))) s ≤ scan s) →
        UpperAt high z a W ops scan arena → ∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W) scan arena
          (Route.axisSwap i j) (swap (z,(a+1,ops),i.val,j.val)) := by
  obtain ⟨L,E,low,el,rl,lr⟩ := PhysicalWalshCompileElementaryRelease.compileGraded
  obtain ⟨K,R,hk⟩ := PhysicalWalshCompileXorRoute.exists_kit
  let M := max (max L H) R
  have uL : L ≤ M := (le_max_left ..).trans (le_max_left ..)
  have uH : H ≤ M := (le_max_right ..).trans (le_max_left ..)
  have uR : R ≤ M := le_max_right ..
  let cmd (p : Z × SwapArgs) := PhysicalWalshCompileXorSwap.ordered K low (fun k => high (p.1,k)) p.2
  have lo : Effective ltr (fun p : Z × SwapArgs => low p.2) := el.comp Computable.snd
  have rev : Computable (fun p : Z × SwapArgs => PhysicalWalshCompileXorSwap.reverseKey p.2) :=
    (Computable.fst.comp Computable.snd).pair (((Computable.snd.comp Computable.snd).comp Computable.snd).pair
      ((Computable.fst.comp Computable.snd).comp Computable.snd))
  have l (k) := RegisterSelect.within_mono uL _ (rl k)
  refine ⟨cmd,M,E,K.effective_chain (K.effective_chain (K.effective_chain lo (el.comp rev)) lo) eh,
    fun k => hk.within_chain uR (hk.within_chain uR (hk.within_chain uR (l _) (l _)) (l _))
      (RegisterSelect.within_mono uH _ (rh k)),?_⟩
  intro z a W ops d ed width scan arena space time elem hr i j ji
  have sw := PhysicalWalshCompileXorSwap.runs_command hk (raw:=(a+1,ops))
    (low:=low) (high:=fun k => high (z,k)) (gradedCut (a+1)) scan arena
    (fun _ => min_le_left ..) time (fun s => (le_max_right ..).trans (space s))
    (fun u v uv => (lr a W ops width u v uv d ed).mono (fun t => elem t.shape) (fun t => space t.shape))
    hr i j
  unfold PhysicalWalshCompileXorSwap.command at sw
  dsimp only at sw
  rw [ite_eq_left (show j.val < i.val from ji)] at sw
  exact sw

/-- A single emitter accepts an arbitrary calibration, template and opcode.
Its clock and space apply to all off-diagonal gates of the decoded template. -/
theorem compileAt (high : Z × SwapArgs → Cmd) (front : Z × Raw → Cmd) (eh : Effective ltr high)
    (ef : Effective ltr front) (H F : ℕ) (rh : ∀ k, Within H (high k)) (rf : ∀ k, Within F (front k)) :
    ∃ (route : Z × Raw → Op → Cmd) (N E : ℕ), Effective ltr (Function.uncurry route) ∧
      (∀ k op, Within N (route k op)) ∧ ∀ z a W ops d (arity : 4 ≤ a), E ≤ d →
        (Packed.decode (a+1) ops).i = W → ∀ scan arena, (∀ s, nodeArena a W d s ≤ arena s) →
        (∀ s, arena s ≤ scan s) →
        (∀ s, nodeScan a W d (ElementarySweep.prefixExtra (a+1) (gradedCut (a+1))) s ≤ scan s) →
        UpperAt high z a W ops scan arena → FrontAt front z a W ops scan arena arity →
        PhysicalWalshCompile.Dispatch.XorRuns (fun raw => route (z,raw)) a W ops scan arena := by
  obtain ⟨swap,S,E,es,rs,runSwap⟩ := swaps high eh H rh
  obtain ⟨route,N,eff,reg,conjugate⟩ := PhysicalWalshCompileXorRoute.compileWith swap front es ef (max S F)
    (fun k => RegisterSelect.within_mono (le_max_left ..) _ (rs k))
    (fun k => RegisterSelect.within_mono (le_max_right ..) _ (rf k))
  refine ⟨route,N,E,eff,reg,?_⟩
  intro z a W ops d arity de width scan arena space time elem hi gate op _ hd hs _
  apply conjugate z a W ops scan arena time (fun s => (le_max_right ..).trans (space s))
    (runSwap z a W ops d de width scan arena space time elem hi) _ op hd hs
  intro _
  have axes : Interior.axes a arity =
      (PhysicalWalshCompileXorRoute.targetAxis a,PhysicalWalshCompileXorRoute.sourceAxis a) := by
    apply Prod.ext <;> apply Fin.ext <;>
      simp [Interior.axes,PhysicalWalshCompileXorRoute.targetAxis,PhysicalWalshCompileXorRoute.sourceAxis,
        PhysicalWalshCompileXorRoute.canonicalTarget,PhysicalWalshCompileXorRoute.canonicalSource,
        show 2<a+1 by omega]
  unfold FrontAt at gate
  rw [axes] at gate
  exact gate

/-- The specialized clock for a calibrated rectangle and front gate. -/
theorem compile (high : Z × SwapArgs → Cmd) (front : Z × Raw → Cmd) (eh : Effective ltr high)
    (ef : Effective ltr front) (H F : ℕ) (rh : ∀ k, Within H (high k)) (rf : ∀ k, Within F (front k)) :
    ∃ (route : Z × Raw → Op → Cmd) (N E : ℕ), Effective ltr (Function.uncurry route) ∧
      (∀ k op, Within N (route k op)) ∧ ∀ z a W ops d ρ (arity : 4 ≤ a), E ≤ d →
        (Packed.decode (a+1) ops).i = W → Upper high z a W ops d ρ → Front front z a W ops d ρ arity →
        PhysicalWalshCompile.Dispatch.XorRuns (fun raw => route (z,raw)) a W ops
          (nodeScan a W d (extra a W ρ)) (nodeArena a W d) := by
  obtain ⟨route,N,E,he,hr,run⟩ := compileAt high front eh ef H F rh rf
  refine ⟨route,N,E,he,hr,?_⟩
  intro z a W ops d ρ arity de width hi gate
  apply run z a W ops d arity de width _ _ (fun _ => le_rfl) (fun _ => Nat.le_add_right ..)
    (fun _ => Nat.add_le_add_left ((Nat.le_add_right ..).trans (Nat.le_add_right ..)) _)
  · intro u v uv
    exact (hi u v uv).mono (fun _ => Nat.add_le_add_left ((Nat.le_add_left ..).trans (Nat.le_add_right ..)) _)
      (fun _ => le_rfl)
  · exact gate.mono (fun _ => Nat.add_le_add_left (Nat.le_add_left ..) _) (fun _ => le_rfl)

end PhysicalWalshEffectiveRoutes

end NearSquareRoot
end Computability
end OAI
