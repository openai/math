import OAI.Computability.NearSquareRoot.PhysicalWalshGroupedFixed
import OAI.Computability.NearSquareRoot.PhysicalWalshPaddingCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshGroupedRate

/-! # Effective grouped selected-Walsh command

A single emitter attaches the grid width, pads the spectator rows, runs the supplied
even-piece command, restores the original length, and dispatches the terminal
parity branch. The varying parameters enter the padding interpreter as literals.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GroupedCommand

open IntegerMultiplication Code Space FixedPoint KernelPass CommonRegisters GeneratorSyntax
open EffectiveBoundedTask KernelEffectiveFamily Filter Pieces

private theorem joinRun {I : Type} {u v w : I → Tree} {t r t' r' : I → ℕ} {c d : Cmd}
    (f : EffectiveBoundedTask.Runs c t r u v) (g : EffectiveBoundedTask.Runs d t' r' v w) :
    EffectiveBoundedTask.Runs (c.join d) (fun i => t i+t' i) (fun i => max (r i) (r' i)) u w :=
  command_contract (c.join d) from f.task.compose g.task

private theorem parkRun {I : Type} {u v : I → Tree} {t r : I → ℕ} {c : Cmd}
    (f : EffectiveBoundedTask.Runs c t r u v) (z : I → Tree) :
    EffectiveBoundedTask.Runs (rightCmd c) (fun i => (z i).count+t i) (fun i => r i+(z i).count)
      (fun i => .fork (z i) (u i)) (fun i => .fork (z i) (v i)) :=
  command_contract (rightCmd c) from f.task.right z

private theorem conformRun {I : Type} {u v u' v' : I → Tree} {t r t' r' : I → ℕ} {c : Cmd}
    (f : EffectiveBoundedTask.Runs c t r u v) (ht : ∀ i,t i=t' i) (hr : ∀ i,r i=r' i)
    (hu : ∀ i,u i=u' i) (hv : ∀ i,v i=v' i) : EffectiveBoundedTask.Runs c t' r' u' v' :=
  (funext ht) ▸ (funext hr) ▸ (funext hu) ▸ (funext hv) ▸ f

noncomputable def boundaryCmd (pad sweep : Cmd) : Cmd :=
  ((((beginCmd.join (rightCmd pad)).join enterCmd).join (rightCmd sweep)).join leaveCmd).join
    (rightCmd trimCmd)

/-- Attach the fixed grid controller and execute the terminal parity butterfly. -/
noncomputable def groupedCmd (pad sweep : Cmd) : Cmd :=
  (makeWidthCmd.join (boundaryCmd pad sweep)).join oddCmd

/-- The emitter specializes the padding setup to the two outer parameters. -/
noncomputable def command (A W : ℕ) (sweep : Cmd) : Cmd :=
  groupedCmd (PaddingCommand.padCmd A W) sweep

variable {I : Type}
theorem boundaries (A W : ℕ) (hA : 1<A) (hw : 0<W) (cSweep : Cmd) (k s w : I → ℕ) (x y : (i : I) → ℕ → Dusk.Grain (w i))
    (sel : ∀ i,s i≤k i) (occ : ∀ i,PaddingHeader.extra A W (k i) (s i) ≤ 2^k i)
    (t r : I → ℕ) :
    let h i := ((tally (k i),tally (s i)),tally (w i+1))
    let n i := 2^k i
    let m i := extent A W (k i) (s i)
    let V i := n i*(w i+1)
    EffectiveBoundedTask.Runs cSweep t r (fun i => send (h i,words (m i) (zeroAfter (n i) (x i))))
      (fun i => send (words (m i) (y i))) →
    EffectiveBoundedTask.Runs (boundaryCmd (PaddingCommand.padCmd A W) cSweep) (fun i => V i+t i) (fun i => V i+r i) (fun i => send (h i,words (n i) (x i)))
      (fun i => send ((tally (k i),tally (s i)),words (n i) (y i))) := by
  intro h n m V sweep
  let e i := PaddingHeader.extra A W (k i) (s i)
  have mEq (i : I) : n i + e i = m i := Padding.total A hw (sel i)
  let init i := (h i,words (n i) (x i))
  let full i := (h i,(tally (n i),words (m i) (zeroAfter (n i) (x i))))
  let tail i := (((h i).1,tally (n i)),words (m i) (y i))
  let f i := (List.range (n i)).map (x i)
  have pad₀ := PaddingCommand.runs A W hA k s w f (by intro i; simp [f,n]) sel occ
  have pad : EffectiveBoundedTask.Runs (PaddingCommand.padCmd A W) V V (fun i => send ((h i).1,words (n i) (x i)))
      (fun i => send (tally (n i),words (m i) (zeroAfter (n i) (x i)))) := by
    apply conformRun pad₀ (fun _ => rfl) (fun _ => rfl) _ _
    · intro i; simp only [f,words,List.map_map,h,n]
    · intro i; rw [← mEq i,padded_words]
  have trim₀ := trimRuns w n (fun i => (List.range (m i)).map (y i)) (by
    intro i; simp only [List.length_map,List.length_range]; have := mEq i; omega)
  have trim : EffectiveBoundedTask.Runs trimCmd (fun i => (m i+1)*(w i+1)) (fun i => (m i+1)*(w i+1))
      (fun i => send (tally (n i),words (m i) (y i))) (fun i => send (words (n i) (y i))) := by
    apply conformRun trim₀ _ _ _ _
    · intro i; simp only [List.length_map,List.length_range]
    · intro i; simp only [List.length_map,List.length_range]
    · intro i; simp only [words,List.map_map]
    · intro i; rw [take_words (show n i ≤ m i by have := mEq i; omega)]
  have a := beginRuns init
  have c := enterRuns full
  have e' := leaveRuns tail
  have chain := joinRun (joinRun (joinRun (joinRun (joinRun a (parkRun pad (fun i => send (h i)))) c)
    (parkRun sweep (fun i => send ((h i).1,tally (n i))))) e') (parkRun trim (fun i => send (h i).1))
  exact chain.bound 200 200
    (fun i => (boundaryBudget A W hw k s w x y sel occ t r i).1)
    (fun i => (boundaryBudget A W hw k s w x y sel occ t r i).2)

/-- Time and peak occupancy of the named command on an indexed family of roots. -/
theorem groupedPass {a W : ℕ} (hw : 0<W) (p : Plan (a+1) W W) (ha : 1 < a+1) (cSweep : Cmd)
    (k s : I → ℕ) (x : (i : I) → ℕ → Record (k i)) (sel : ∀ i,s i ≤ k i)
    (occ : ∀ i,PaddingHeader.extra (a+1) W (k i) (s i) ≤ 2^k i)
    (t r : I → ℕ) :
    let b i := root (k i) (s i) (x i)
    EffectiveBoundedTask.Runs cSweep t r (fun i => send (((tally (k i),tally (s i)),tally (componentBits (k i)+1)),
        words ((b i).size (a:=a) (W:=W)) (b i).row))
      (fun i => send ((b i).stream hw p ((b i).pieces (a:=a) hw).length)) →
    EffectiveBoundedTask.Runs (command (a+1) W cSweep) (fun i => t i+Odd.time (k i)) (fun i => r i+Odd.volume (k i))
      (fun i => send ((tally (k i),tally (s i)),words (2^k i) (x i)))
      (fun i => send (Odd.words (result hw p (k i) (s i) (x i)))) := by
  intro b sweep
  let y i := (b i).stage hw p ((b i).pieces (a:=a) hw).length
  have centered := GroupedCommand.boundaries (a+1) W ha hw cSweep k s (fun i => componentBits (k i)) x y sel occ t r sweep
  have whole := joinRun (joinRun (makeWidthRuns k s sel x) centered) (oddRuns k s sel y)
  apply whole.bound 110 110 <;> intro i
  all_goals
    have ratio : 2^k i*(componentBits (k i)+1) ≤ 96*Odd.volume (k i) := by
      unfold Odd.volume componentBits; ring_nf; omega
    have vt : Odd.volume (k i) ≤ Odd.time (k i) := Nat.mul_le_mul_left _ (GridTask.width_le_recordCost _)
  · change Odd.volume (k i)+(2^k i*(componentBits (k i)+1)+t i)+Odd.time (k i)+1 ≤ _
    omega
  · change max (max (Odd.volume (k i)) (2^k i*(componentBits (k i)+1)+r i)) (Odd.volume (k i))+1 ≤ _
    omega

/-- Sparse time and linear space survive all finite-grid boundary operations. -/
theorem sparse {a W : ℕ} (hw : 0<W) (p : Plan (a+1) W W) (ha : 1 < a+1) (cSweep : Cmd)
    (k s : I → ℕ) (x : (i : I) → ℕ → Record (k i)) (sel : ∀ i,s i ≤ k i)
    (occ : ∀ i,PaddingHeader.extra (a+1) W (k i) (s i) ≤ 2^k i)
    {ρ : ℝ} (hr : 0 ≤ ρ) :
    let b i := root (k i) (s i) (x i)
    EffectiveBoundedTask.Runs cSweep (sparseTime ρ ∘ k) (sparseSpace ∘ k)
      (fun i => send (((tally (k i),tally (s i)),tally (componentBits (k i)+1)),
        words ((b i).size (a:=a) (W:=W)) (b i).row))
      (fun i => send ((b i).stream hw p ((b i).pieces (a:=a) hw).length)) →
    EffectiveBoundedTask.Runs (command (a+1) W cSweep) (sparseTime ρ ∘ k) (sparseSpace ∘ k)
      (fun i => send ((tally (k i),tally (s i)),words (2^k i) (x i)))
      (fun i => send (Odd.words (result hw p (k i) (s i) (x i)))) := by
  intro b h
  have run := GroupedCommand.groupedPass hw p ha cSweep k s x sel occ _ _ h
  obtain ⟨D,ht⟩ := odd_time_le hr
  exact run.bound (D+1) 3
    (fun i => by dsimp only [Function.comp_apply]; rw [Nat.succ_mul]; have := ht (k i); omega)
    (fun i => by dsimp only [Function.comp_apply]; have := odd_volume_le (k i); omega)

/-- Effective in both geometric parameters and the complete even command file. -/
theorem effective {P : Type} [Primcodable P] {A W : P → ℕ} {c : P → Cmd}
    (hA : Computable A) (hW : Computable W) (hc : Effective ltr c) :
    Effective ltr (fun p => command (A p) (W p) (c p)) := by
  have ep := PaddingCommand.effective.comp (hA.pair hW)
  have linked := (((((effective_const ltr beginCmd).join (effective_right ep)).join
    (effective_const ltr enterCmd)).join (effective_right hc)).join (effective_const ltr leaveCmd)).join
    (effective_right (effective_const ltr trimCmd))
  exact ((effective_const ltr makeWidthCmd).join linked).join (effective_const ltr oddCmd)

/-- There is one register high-water mark for the complete controller surrounding any sweep. -/
theorem within : ∃ B : ℕ, 0 < B ∧ ∀ R, B ≤ R → ∀ A W (c : Cmd), Within R c →
    Within R (command A W c) := by
  obtain ⟨P,_,pad⟩ := PaddingCommand.within
  have large : ∀ᶠ R : ℕ in atTop, 3 ≤ R ∧ P ≤ R ∧ Within R beginCmd ∧ Within R enterCmd ∧
      Within R leaveCmd ∧ Within R trimCmd ∧ Within R makeWidthCmd ∧ Within R oddCmd := by
    filter_upwards [eventually_ge_atTop 3,eventually_ge_atTop P,RegisterSelect.within_eventually beginCmd,
      RegisterSelect.within_eventually enterCmd,RegisterSelect.within_eventually leaveCmd,
      RegisterSelect.within_eventually trimCmd,RegisterSelect.within_eventually makeWidthCmd,
      RegisterSelect.within_eventually oddCmd] with R h₃ hp b e l t w o
    exact ⟨h₃,hp,b,e,l,t,w,o⟩
  obtain ⟨B,hB⟩ := eventually_atTop.mp large
  refine ⟨max 3 B,by omega,fun R hR A W c hc => ?_⟩
  obtain ⟨h₃,hp,b,e,l,t,w,o⟩ := hB R (by omega)
  have pp := RegisterSelect.within_mono hp _ (pad A W)
  exact ⟨⟨w,⟨⟨⟨⟨⟨b,within_right h₃ pp⟩,e⟩,within_right h₃ hc⟩,l⟩,within_right h₃ t⟩⟩,o⟩

end PhysicalWalsh.GroupedCommand

end NearSquareRoot
end Computability
end OAI
