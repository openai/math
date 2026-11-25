import OAI.Computability.NearSquareRoot.InterchangeBQuestResolve

/-!
# Combining small recursive calls with a full-volume reserve schedule

One command first executes the bounded main bank and then runs the prepared
reserve schedule. Local bank data may remain parked during the small calls.
The full-volume calls carry only the remaining header forest and one pending
return. Both phases call the same recursive command.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  IntegerMultiplication.Strip NearSquareRoot.Space NearSquareRoot.InterchangeBatch

variable {I X : Type}

structure CenterBody (r : Regime I) (n l : I → ℕ) (job : Job X)
    (small full : I → List X) (park : I → ℕ) (input output : I → Tree) : Prop where
  build : ∃ k K : ℕ, ∃ cmd : Cmd, ∀ i (parent : Cmd) (env : Env) (time data depth : X → ℕ),
    (∀ y ∈ small i ++ full i, ∀ d b, DeckCap b d →
      BoundedFits (parent::env) parent (pile 0 (job.issue y) d) (pile 0 (job.reply y) d)
        (time y) (b+data y) (depth y)) → ∀ d base, DeckCap base d →
    let L := K*(massNat r n l k i + 1)
    BoundedFits (parent::env) cmd (pile 0 (input i) d) (pile 0 (output i) d)
      (L + (((small i ++ full i).map time).sum))
      (base + max (L + childPeak data (small i)) (park i + childPeak data (full i)))
      (max (L + childPeak depth (small i)) (1 + childPeak depth (full i)))

namespace CenterBody

variable {r : Regime I} {n l : I → ℕ} {job : Job X} {small full : I → List X}
    {input output : I → Tree}

/-- Compile a bounded main bank and an explicit tail schedule, using the
parent header to generate the reserve headers after the main bank returns. -/
theorem of_batch (header payload : X → Tree) (issue : ∀ z, job.issue z = .fork (header z) (payload z))
    (source : I → Tree) (V : I → ℕ) (main : BQuest job r n l small input (together r.header source))
    (tags : r.Small (fun i => headers header (full i)))
    (chain : ∀ i, Chain payload job.reply (source i) (full i) (output i))
    (hx : ∀ i z, z ∈ full i → (payload z).count ≤ V i) (hy : ∀ i, (output i).count ≤ V i)
    (outerBudget : ∀ u : I → ℕ, Dom r.scale u → ∃ k C : ℕ, ∀ i,
      (r.header i).count + (source i).count + V i + u i + (headers header (full i)).count +
        (full i).length + 1 ≤ C*(massNat r n l k i+1)) :
    CenterBody r n l job small full (fun i => (headers header (full i)).count) input output := by
  obtain ⟨j,⟨cmd,A,run⟩⟩ := main.eligible
  obtain ⟨u,hu,prep,K,post⟩ := prepared_recursive_batch header payload job.reply source output full tags chain
  obtain ⟨d,C,volume⟩ := outerBudget u hu
  let coeff := A + (K+120)*C + 12
  refine ⟨max j d,coeff,cmd.join (prep.join (batch (.again 1))),?_⟩
  intro i parent env time data depth children deck base hc
  let M := massNat r n l (max j d) i + 1
  let L := coeff*M
  let H := (headers header (full i)).count
  let S := childPeak data (small i)
  let D := childPeak depth (small i)
  let F := childPeak data (full i)
  let R := childPeak depth (full i)
  let T := K*(u i+1)
  let Z := A*(massNat r n l j i+1)
  have size := (volume i).trans (Nat.mul_le_mul_left C
    (Nat.add_le_add_right (massNat_mono r n l (le_max_right j d) i) 1))
  change (r.header i).count + (source i).count + V i + u i + H + (full i).length + 1 ≤ C*M at size
  have smallCost : Z ≤ A*M :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (massNat_mono r n l (le_max_left j d) i) 1)
  have prepCost : T ≤ K*(C*M) := Nat.mul_le_mul_left _ (by omega)
  have combined :
      Z + T + V i + (r.header i).count + (source i).count + 110*(H+1) + (full i).length + 10 ≤ L := by
    have positive : 1 ≤ M := Nat.succ_pos _
    have eq : L = A*M + K*(C*M) + 120*(C*M) + 12*M := by dsimp only [L,coeff]; ring
    omega
  have left := run i parent env time S D (fun y hy stack b hb =>
    (children y (List.mem_append_left _ hy) stack b hb).mono le_rfl
      (Nat.add_le_add_left (le_childPeak data hy) b) (le_childPeak depth hy)) deck base hc
  change BoundedFits _ _ _ _ (Z+_) (base+Z+S) (Z+D) at left
  have right := post i parent env time data depth (V i) (hx i) (hy i) (fun y hy stack b hb => by
    simpa only [issue] using children y (List.mem_append_right _ hy) stack b hb) deck base hc
  change BoundedFits _ _ _ _ (T+(_+_+110*(H+1))+2)
      (base+max ((Tree.fork (r.header i) (source i)).count+T) (dataSpace (V i) H F))
      (max (T+1) (returnSpace H R)) at right
  let totalCap := base + max (L+S) (H+F)
  let totalRet := max (L+D) (1+R)
  have h₁ : L+S ≤ max (L+S) (H+F) := le_max_left ..
  have h₂ : H+F ≤ max (L+S) (H+F) := le_max_right ..
  have h₃ : L+D ≤ totalRet := le_max_left ..
  have h₄ : 1+R ≤ totalRet := le_max_right ..
  have lrun := left.mono le_rfl (show base+Z+S ≤ totalCap by dsimp only [totalCap]; omega) le_rfl
  have rrun := right.mono le_rfl (show _ ≤ totalCap by
    dsimp only [totalCap, dataSpace, Tree.count]; omega) (show _ ≤ totalRet by
    dsimp only [returnSpace]; omega)
  apply (lrun.join rrun (by omega)).mono _ le_rfl le_rfl
  simp only [List.map_append, List.sum_append]
  change _ ≤ L + (_ + _)
  omega

end CenterBody
end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
