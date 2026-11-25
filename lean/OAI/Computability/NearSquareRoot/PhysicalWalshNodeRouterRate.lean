import OAI.Computability.NearSquareRoot.PhysicalWalshNodeMachine
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRate

/-! # Releasing the routed recursive Walsh machine at the selected-piece rate

The interleaving permutation supplies its own physical command and additional
scan bound. The fixed program constructs all other operations, including the
terminal transform, descriptor updates, and arithmetic, from the kernel plan.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code Space PhysicalWalsh KernelPass

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

/-- The charge recurrence, its closed-form bound, and its realization by a
single finite multitape machine. The physical clock includes the output copy. -/
def PieceRelease (ρ c : ℝ) (L P : ℕ → ℝ) : Prop :=
  let s := fun v : Admitted hw p => v.val.shape
  BoundedTask (pieceTime (a+1) W p.calls ρ c L P ∘ s) (pieceSpace (a+1) W c P ∘ s)
      (rawInput hw p) (rawOutput hw p) ∧
    ∃ B : ℝ, 0 ≤ B ∧
      let T := pieceTimeBound (a+1) p.calls ρ B L P ∘ s
      let S := pieceSpaceBound (a+1) c P ∘ s
      BoundedTask T S (rawInput hw p) (rawOutput hw p) ∧
        ∃ C : ℕ, TapeRun (fun v => C*(T v+1)) (fun v => C*(S v+1)) (rawInput hw p) (rawOutput hw p)

/-- One degree and one arena coefficient suffice for all occupied roots.
Given the physical XOR implementation, the only rate assumption concerns its
extra scans at a node. Its live records use the same arena as the arithmetic. -/
theorem routedPieceRelease (arity : 2 ≤ a+1) (wide : 2 ≤ W) {ρ : ℝ} (hr : 0 ≤ ρ)
    (saving : (p.calls : ℝ)/W < ((a+1 : ℕ):ℝ)^ρ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d, D ≤ d → ∃ K : ℕ, 1 ≤ K ∧ ∀ (extra : Shape → ℕ),
    XorRuns a W (nodeScan a W d extra) (nodeArena a W d) → ∀ (c : ℝ) (L P : ℕ → ℝ),
    0 ≤ c → (∀ w, 1 ≤ L w) → (∀ w, 0 ≤ P w) →
    (∀ s, withinWidth (a+1) s → (extra s : ℝ) ≤
      localTime (a+1) ρ c (L s.w) (P s.w) s.level (bitVolume (a+1) s)) →
    PieceRelease hw p ρ (4*K+c) L (envelopeSetup K d P) := by
  obtain ⟨D,hD,programs⟩ := localPrograms hw p
  refine ⟨D,hD,fun d hd => ?_⟩
  obtain ⟨K,hK,cap⟩ := max_arena_allowance_le a W d (hD.trans hd)
  refine ⟨K,hK,fun extra xor c L P hc hL hP router => ?_⟩
  let arena := nodeArena a W d
  let scan := nodeScan a W d extra
  have cost (s) : arena s ≤ scan s := Nat.le_add_right ..
  have capacity (s) : allowance (a+1) D s ≤ arena s := (allowance_mono hd s).trans (le_max_left ..)
  have init (s) : allowance (a+1) 1 s ≤ arena s := (allowance_mono hD s).trans (capacity s)
  have prog : Programs hw p scan arena cost := programs scan arena cost capacity (fun _ => le_max_right ..) xor
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
  have task := rawPiece hw p scan arena cost prog (fun s _ => init s) ρ G L Q gc l time space
  obtain ⟨B,hB,bound⟩ := pieceTime_le (by omega : 1 ≤ a+1) hw hr gc saving
  have T (s) := bound L Q l q s
  have bounded := task.mono (fun v => T v.val.shape) (fun v => pieceSpace_le wide gc q v.val.shape)
  refine ⟨task,B,hB,bounded,releasePiece hw p bounded (fun v => ?_)⟩
  apply (init _).trans ((cost _).trans ?_)
  apply le_trans _ (T v.val.shape)
  have base : scan v.val.shape ≤ ⌊localTime (a+1) ρ G (L v.val.shape.w) (Q v.val.shape.w)
      v.val.shape.level (bitVolume (a+1) v.val.shape)⌋₊ :=
    Nat.le_floor ((le_add_of_nonneg_right zero_le_one).trans (time _ v.property))
  apply base.trans
  change _ ≤ PhysicalWalsh.charge W p.calls _ v.val.shape.level _
  cases v.val.shape.level <;> simp [PhysicalWalsh.charge]

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
