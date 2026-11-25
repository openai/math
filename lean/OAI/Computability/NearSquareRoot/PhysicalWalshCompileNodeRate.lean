import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeTrace
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouterRate
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Time and workspace of the emitted program for a selected Walsh piece -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Node

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode KernelPass

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

open private local_le_charge from OAI.Computability.NearSquareRoot.PhysicalWalshNodeRate

/-- The integral charges for time and peak workspace apply to the very
program returned by the compiler, with the initial query tag included. -/
theorem rawPieceNamed (cmd : Cmd) (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)
    (run : NamedTrace hw p scan arena cost cmd)
    (capacity : ∀ s, withinWidth (a+1) s → allowance (a+1) 1 s ≤ arena s)
    (ρ c : ℝ) (L P : ℕ → ℝ) (hc : 0 ≤ c) (hL : ∀ w, 0 ≤ L w)
    (ht : ∀ s, withinWidth (a+1) s → (scan s : ℝ)+1 ≤
      localTime (a+1) ρ c (L s.w) (P s.w) s.level (bitVolume (a+1) s))
    (hs : ∀ s, withinWidth (a+1) s → (arena s : ℝ)+1 ≤
      localSpace c (P s.w) s.level (bitVolume (a+1) s)) :
    EffectiveBoundedTask.Runs (entry.join cmd)
      (fun v : Admitted hw p => pieceTime (a+1) W p.calls ρ c L P v.val.shape)
      (fun v => pieceSpace (a+1) W c P v.val.shape) (rawInput hw p) (rawOutput hw p) := by
  let vm := spec hw p scan arena cost
  let d := vm.restrict (withinWidth (a+1))
  let l := (chargeLayout hw p scan arena cost).restrict (withinWidth (a+1))
  let u (v : Admitted hw p) := v.val.shape
  let T (v : Admitted hw p) := pieceTime (a+1) W p.calls ρ c L P (u v)
  let S (v : Admitted hw p) := pieceSpace (a+1) W c P (u v)
  let query (v : Admitted hw p) := vm.query v.val
  have tag := entry_shape (fun _ : Admitted hw p => a+1) u (fun v => v.val.row)
  have tagged : EffectiveBoundedTask.Runs entry T S (rawInput hw p) query := by
    apply tag.mono
    · intro v
      have h := Nat.le_floor ((le_add_of_nonneg_right zero_le_one).trans (ht _ v.property))
      exact (capacity _ v.property).trans ((cost _).trans (h.trans (local_le_charge ..)))
    · intro v
      have h := Nat.le_floor ((le_add_of_nonneg_right zero_le_one).trans (hs _ v.property))
      exact (capacity _ v.property).trans (h.trans (local_le_charge ..))
  apply tagged.sequence
  obtain ⟨D,exec⟩ := run
  let t := fun w => localTime (a+1) ρ c (L w) (P w)
  let s := fun w => localSpace c (P w)
  have cert := l.recurrence (C := 1) (calls := p.calls) t s
    (fun w => localTime_mono hc (hL w)) (fun _ => localSpace_mono hc)
    (fun v => by simp only [one_mul,Nat.cast_add,Nat.cast_one]; exact ht v.val v.property)
    (fun v => by simp only [one_mul,Nat.cast_add,Nat.cast_one]; exact hs v.val v.property)
  have scaled := cert.scale D
  simp only [Nat.mul_one] at scaled
  refine ⟨D,fun v env park b hb => ?_⟩
  have h := exec _ _ scaled v env park b hb
  exact h.mono (Nat.mul_le_mul_left D (Nat.le_succ _))
    (Nat.add_le_add_left (Nat.mul_le_mul_left D (Nat.le_succ _)) b)
    (Nat.mul_le_mul_left D (Nat.le_succ _))

/-- A single command on all admitted inputs meets the closed-form time and
workspace bounds for a strictly saving selected-bit template. -/
theorem routedNamedPieceRate (d : ℕ) (hd : 1 ≤ d)
    (arity : 2 ≤ a+1) (wide : 2 ≤ W) {ρ : ℝ} (hr : 0 ≤ ρ)
    (saving : (p.calls : ℝ)/W < ((a+1 : ℕ):ℝ)^ρ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (extra : Shape → ℕ) (cmd : Cmd),
    NamedTrace hw p (nodeScan a W d extra) (nodeArena a W d) (fun _ => Nat.le_add_right ..) cmd →
    ∀ (c : ℝ) (L P : ℕ → ℝ), 0 ≤ c → (∀ w, 1 ≤ L w) → (∀ w, 0 ≤ P w) →
    (∀ s, withinWidth (a+1) s → (extra s : ℝ) ≤
      localTime (a+1) ρ c (L s.w) (P s.w) s.level (bitVolume (a+1) s)) →
    ∃ B : ℝ, 0 ≤ B ∧ EffectiveBoundedTask.Runs (entry.join cmd)
      (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls ρ B L (envelopeSetup K d P) v.val.shape)
      (fun v => pieceSpaceBound (a+1) (4*K+c) (envelopeSetup K d P) v.val.shape)
      (rawInput hw p) (rawOutput hw p) := by
  obtain ⟨K,hK,cap⟩ := max_arena_allowance_le a W d hd
  refine ⟨K,hK,fun extra cmd trace c L P hc hL hP router => ?_⟩
  let arena := nodeArena a W d
  let scan := nodeScan a W d extra
  let G : ℝ := 4*K+c
  let Q := envelopeSetup K d P
  have gc : 0 ≤ G := by dsimp [G]; positivity
  have l (w) : 0 ≤ L w := zero_le_one.trans (hL w)
  have q (w) : 0 ≤ Q w := envelopeSetup_nonneg K d hP w
  have time (s : Shape) (h : withinWidth (a+1) s) : (scan s:ℝ)+1 ≤
      localTime (a+1) ρ G (L s.w) (Q s.w) s.level (bitVolume (a+1) s) :=
    scan_envelope arity h (hL s.w) (Nat.add_le_add_right (cap s) (extra s)) (router s h)
  have space (s : Shape) (h : withinWidth (a+1) s) : (arena s:ℝ)+1 ≤
      localSpace G (Q s.w) s.level (bitVolume (a+1) s) := by
    apply arena_envelope (extra := 0) arity h
    · simpa only [arena,nodeArena,Nat.add_zero] using cap s
    · exact_mod_cast add_nonneg (mul_nonneg hc (bitVolume_nonneg _ _)) (hP s.w)
  have task := rawPieceNamed hw p cmd scan arena (fun _ => Nat.le_add_right ..) trace
    (fun s _ => (allowance_mono hd s).trans (le_max_left ..)) ρ G L Q gc l time space
  obtain ⟨B,hB,clock⟩ := pieceTime_le (by omega : 1 ≤ a+1) hw hr gc saving
  exact ⟨B,hB,task.mono (fun v => clock L Q l q v.val.shape) (fun v => pieceSpace_le wide gc q v.val.shape)⟩

end PhysicalWalshCompile.Node

end NearSquareRoot
end Computability
end OAI
