import OAI.Computability.NearSquareRoot.PhysicalWalshRelease
import OAI.Computability.NearSquareRoot.BoundedProgramForget
import OAI.Computability.IntegerMultiplication.Code.Carry

/-! # Changing a serialized Walsh bank's shape header during a linear scan

The original descriptor is retained while a temporary field controls the
stream transform. A second expanded header accompanies the resulting bank.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code Space

variable {I H K G A B : Type} [Codec H] [Codec K] [Codec G] [Codec A] [Codec B]
  {V : I → ℕ} {q r : I → Tree}

private theorem toCarries (h : BoundedTask V V q r) : Carries (fun i => (V i:ℝ)+1) q r := by
  obtain ⟨C,cap⟩ := h.endpointSize
  refine ⟨Sized.natural h.forget,C,fun i => ?_⟩
  change ((q i).count : ℝ) ≤ C * ((V i : ℝ)+1)
  exact_mod_cast (le_max_left ..).trans (cap i)

private theorem ofCarries (h : Carries (fun i => (V i:ℝ)+1) q r) : BoundedTask V V q r := by
  obtain ⟨D,cap⟩ := h.small
  have c : Task (fun i => V i + 1) q r := by
    simpa only [← Nat.cast_add_one, Nat.ceil_natCast] using h.runs.release
  apply (BoundedTask.of_time c).bound 2 (D+2) <;> intro i
  · omega
  · have hc := cap i
    change ((q i).count : ℝ) ≤ D * ((V i : ℝ)+1) at hc
    have z : (q i).count ≤ D*(V i+1) := by exact_mod_cast hc
    rw [Nat.add_mul]; omega

variable (h : I → H) (k : I → K) (g : I → G) (a : I → A) (b : I → B)
  (cuts : BoundedTask V V (send ∘ h) (send ∘ k)) (grid : BoundedTask V V (send ∘ h) (send ∘ g))
  (transform : BoundedTask V V (fun i => send (k i,a i)) (fun i => send (k i,b i)))

include cuts grid transform

set_option maxHeartbeats 1200000 in
/-- Lift a header-preserving stream transform to a descriptor input. Both
physical header programs and the scan run on the same fixed machine. -/
theorem framePrepare : BoundedTask V V (fun i => send (h i,a i))
    (fun i => send ((g i,h i),b i)) := by
  let v i := (V i:ℝ)+1
  have ck := toCarries cuts
  have cg := toCarries grid
  have ct := toCarries transform
  have keep := Carries.idles cg.budget cg.small
  have keys := ck.twice (cg.twice keep)
  have av := (show Volume v (fun i => Tree.fork (send (k i)) (send (a i))) from ct.small).right
  have initial : Carries v (fun i => send (h i,a i)) (fun i => send ((k i,g i,h i),a i)) := keys.first av
  let prepare (z : (K × G × H) × A) := ((z.1.1,z.2),z.1.2)
  let finish (z : (K × B) × (G × H)) := (z.2,z.1.2)
  have ep : Easy prepare := ((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)
  have ef : Easy finish := Easy.snd.pair (Easy.fst.compose Easy.snd)
  have opening : Carries v (fun i => send (h i,a i)) (fun i => send ((k i,a i),g i,h i)) :=
    initial.chain (Carries.func initial.budget initial.out prepare ep)
  have run : Carries v (fun i => send (h i,a i)) (fun i => send ((k i,b i),g i,h i)) :=
    opening.chain (ct.first (cg.out.fork cg.small cg.budget))
  have close := run.chain (Carries.func run.budget run.out finish ef)
  exact ofCarries close

set_option maxHeartbeats 1200000 in
/-- Return the transformed stream to its compact-descriptor boundary. -/
theorem frameRestore : BoundedTask V V (fun i => send ((g i,h i),a i))
    (fun i => send (h i,b i)) := by
  let v i := (V i:ℝ)+1
  have ck := toCarries cuts
  have cg := toCarries grid
  have ct := toCarries transform
  have av := (show Volume v (fun i => Tree.fork (send (k i)) (send (a i))) from ct.small).right
  let discardGrid {Z : Type} (z : (G × H) × Z) := (z.1.2,z.2)
  have discard {Z : Type} [Codec Z] : Easy (discardGrid (Z := Z)) :=
    (Easy.fst.compose Easy.snd).pair Easy.snd
  have first : Carries v (fun i => send ((g i,h i),a i)) (fun i => send (h i,a i)) :=
    Carries.func cg.budget ((cg.out.fork ck.small cg.budget).fork av cg.budget) discardGrid discard
  let keep (z : (H × H) × B) := (z.1.2,z.2)
  have keepEasy : Easy keep := (Easy.fst.compose Easy.snd).pair Easy.snd
  have idle := ofCarries (h := Carries.idles ck.budget ck.small)
  have stage := first.chain (toCarries (framePrepare h k h a b cuts idle transform))
  exact ofCarries (stage.chain (Carries.func stage.budget stage.out keep keepEasy))

end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
