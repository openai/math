import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedAt
import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshGroupedCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshSparseCommand

/-! # Emitted selected-Walsh program in original record order

The source file combines the mask scanner, both position permutations, physical
padding, the agenda of even pieces and its odd-bit terminal branch. The two
source parameters are the position router and the recursive piece evaluator.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code FixedPoint KernelPass PhysicalWalshNode Matrix
open CommonRegisters GeneratorSyntax

/-- Source of the entire masked pass, including all shape-dependent setup. -/
noncomputable def planCmd (A W : ℕ) (router piece : Cmd) : Cmd :=
  selectedCmd router (GroupedCommand.command A W (Pieces.sweepCmd A W piece))

theorem planCmd_effective {P : Type} [Primcodable P] {A W : P → ℕ} {router piece : P → Cmd}
    (hA : Computable A) (hW : Computable W) (hr : Effective ltr router) (hp : Effective ltr piece) :
    Effective ltr (fun p => planCmd (A p) (W p) (router p) (piece p)) :=
  selectedCmd_effective hr (GroupedCommand.effective hA hW (Pieces.sweepCmd_effective hA hW hp))

/-- The register bound is independent of the radix, fanout and input width. -/
theorem planCmd_within (r : ℕ) : ∃ R, 0<R ∧ ∀ A W (router piece : Cmd),
    Within r router → Within r piece → Within R (planCmd A W router piece) := by
  obtain ⟨s,_,sweep⟩ := Pieces.sweepCmd_within r
  obtain ⟨b,_,grouped⟩ := GroupedCommand.within
  let m := max r (max s b)
  obtain ⟨R,hR,selected⟩ := selectedCmd_within m
  refine ⟨R,hR,fun A W router piece hr hp => selected _ _ (RegisterSelect.within_mono (le_max_left ..) _ hr) ?_⟩
  exact grouped m ((le_max_right ..).trans (le_max_right ..)) _ _ _
    (RegisterSelect.within_mono ((le_max_left ..).trans (le_max_right ..)) _ (sweep A W piece hp))

theorem selectedCutoff_primrec {P : Type} [Primcodable P] {r G W M : P → ℕ}
    (hr : Primrec r) (hg : Primrec G) (hw : Primrec W) (hm : Primrec M) :
    Primrec (fun p => selectedCutoff (r p) (G p) (W p) (M p)) :=
  Primrec.nat_max.comp hr (Primrec.nat_max.comp (SparseCutoff.primrec_threshold.comp hg hw)
    (precisionCutoff_primrec.comp hm))

theorem selectedCutoff_computable {P : Type} [Primcodable P] {r G W M : P → ℕ}
    (hr : Computable r) (hg : Computable G) (hw : Computable W) (hm : Computable M) :
    Computable (fun p => selectedCutoff (r p) (G p) (W p) (M p)) :=
  Primrec.nat_max.to_comp.comp hr (Primrec.nat_max.to_comp.comp
    (SparseCutoff.primrec_threshold.to_comp.comp hg hw) (precisionCutoff_primrec.to_comp.comp hm))

/-- Lift the certified emitted passes to a family on a dependent input type. -/
theorem planCmd_family {P : Type} [Primcodable P] {I : P → Type}
    {A W : P → ℕ} {router piece : P → Cmd} {t s : ∀ p, I p → ℕ} {u v : ∀ p, I p → Tree}
    (hA : Computable A) (hW : Computable W) (hr : Effective ltr router) (hp : Effective ltr piece)
    (r : ℕ) (wr : ∀ p, Within r (router p)) (wp : ∀ p, Within r (piece p))
    (run : ∀ p, EffectiveBoundedTask.Runs (planCmd (A p) (W p) (router p) (piece p)) (t p) (s p) (u p) (v p)) :
    EffectiveBoundedTask.Family t s u v := by
  obtain ⟨R,pos,within⟩ := planCmd_within r
  exact ⟨_,R,planCmd_effective hA hW hr hp,pos,fun p => ⟨within _ _ _ _ (wr p) (wp p),run p⟩⟩

/-- At the explicit threshold, the emitted command attains the sparse clock
and linear live-space bounds and approximates the Walsh matrix on exactly
the bits specified by the physical input mask. -/
theorem planPassAt {a W K₀ M G : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    (router piece : Cmd) (correct : Correct p) (factor : recursionFactor p ≤ M)
    {ρ B c : ℝ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hB : 0 ≤ B) (hc : 0 ≤ c) (hP : ∀ w,0 ≤ P w)
    (raw : EffectiveBoundedTask.Runs piece
      (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls ρ B L P v.val.shape)
      (fun v => pieceSpaceBound (a+1) c P v.val.shape) (rawInput hw p) (rawOutput hw p))
    (route : PositionRunsAt router ρ K₀)
    {g H Q : ℝ} {q : ℕ} (hg : 0 < g) (cap : g ≤ G+1) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    {I : Type} (k : I → ℕ) (bits : (i : I) → Finset (Fin (k i)))
    (mask : I → List Bool) (x : (i : I) → Fin (2^k i) → Record (k i))
    (large : ∀ i, selectedCutoff K₀ G W M ≤ k i) (hm : ∀ i, mask i = flags (bits i))
    (sparse : ∀ i, ((bits i).card : ℝ) ≤ g*k i/Real.log (2+k i))
    (norm : ∀ i, ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i))
    (overhead : ∀ i, 0 ≤ L (componentBits (k i)) ∧ L (componentBits (k i)) ≤ H*(1+Real.log (2+k i)))
    (setup : ∀ i, P (componentBits (k i)) ≤ Q*(k i+1:ℝ)^q) :
    EffectiveBoundedTask.Runs (planCmd (a+1) W router piece) (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k)
      (fun i => send (mask i,Odd.words (x i)))
      (fun i => send (Odd.words (selectedResult hw p (bits i) (x i)))) ∧
    ∀ i, ‖recordArray (selectedResult hw p (bits i) (x i)) - WithLp.toLp 2
      (BoxFin.flatWalsh (bits i) *ᵥ (fun j => FixedPoint.value (k i) (x i j)))‖ ≤ 1/(2:ℝ)^(50*k i) := by
  let s i := (bits i).card
  let pos i := gatherPerm (bits i)
  let v i := lift (gatherInput (pos i) (x i))
  let b i := Pieces.root (k i) (s i) (v i)
  have routeLarge i : K₀ ≤ k i := (le_max_left ..).trans (large i)
  have geomLarge i : SparseCutoff.threshold G W ≤ k i := (le_max_left ..).trans ((le_max_right ..).trans (large i))
  have numLarge i : precisionCutoff M ≤ k i := (le_max_right ..).trans ((le_max_right ..).trans (large i))
  have geom i := SparseCutoff.geometry (a+1) hw (geomLarge i) hg cap (sparse i)
  have guards i := accurate_of_cutoff ha hw p correct factor (numLarge i) (bits i) (pos i)
    (gatherPerm_low (bits i)) (x i) (norm i)
  have capacity (i) : (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1) := by
    change Pieces.extent (a+1) W (k i) (s i) ≤ 2^(componentBits (k i)+1)
    unfold Pieces.extent
    rw [←Padding.total (a+1) hw (geom i).1]
    calc
      _ ≤ 2^k i + 2^k i := Nat.add_le_add_left (geom i).2 _
      _ = 2^(k i+1) := by rw [pow_succ]; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold componentBits; omega)
  have wbound (i) : ((b i).w:ℝ) ≤ 96*((b i).k+1) := by
    change ((96*k i+4:ℕ):ℝ) ≤ 96*((k i:ℝ)+1)
    push_cast; linarith
  have even := Pieces.sparseRoundedSweepNamed hw p piece ha hr hB hc hP raw b capacity (fun i => (guards i).1)
    hg (by norm_num : (0:ℝ) ≤ 96) hH hQ sparse wbound overhead setup
  have grouped := GroupedCommand.sparse hw p ha _ k s v (fun i => (geom i).1) (fun i => (geom i).2) hr.le even
  exact ⟨selectedTaskNamed hw p router _ hr.le route k bits mask x routeLarge hm grouped,fun i => (guards i).2⟩

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
