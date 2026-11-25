import OAI.Computability.BorderVNP.PackedInheritedWorkReplay
import OAI.Computability.BorderVNP.PackedHistoryLeafPrograms
import OAI.Computability.BorderVNP.PackedHistoryEpoch

/-! # Readback on the row-major input tuple of a compiled epoch

The entire shared inner gate tree sees the canonical histogram bit tuple.
Its private programs are precisely those in the actual flattened private
replay; the per-child width witnesses follow the same copy ordinals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Diagonal.ExternalSew Diagonal.CellEntries
open Epoch.Round VPVNP.VerifierNetwork
open private leafFrames from OAI.Computability.BorderVNP.PackedHistoryEpoch
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 1500000

variable {D m k b : ℕ} [NeZero D] {K I P : Type} [Field K] [Fintype I] [Fintype P] {bits : P → ℕ}
variable {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ} {e : PaidIdentity K D m}
variable {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
variable (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)
variable {W G : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
variable (codec : Codec F.system G) (step : Steps k b W G) (read : PrivateOutput view W)

omit [NeZero D] [Field K] in
private theorem flat_leaves {σ : Type} [Fintype σ] (x : σ → Bool) (n : ℕ)
    (flat : Fin (k^n) → A 0) (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (f : Fin (k^n) → Frame σ (W 0)) (hr : ∀ i, read 0 (flat i) (pr i) ((f i).eval x)) :
    PrivateLeaves read x n (leavesEquiv k _ n flat) (nestedPrivatePrograms (fun z => (view 0 z).pack) n flat pr)
      (leavesEquiv k _ n f) := by
  induction n with
  | zero =>
    dsimp only [PrivateLeaves,nestedPrivatePrograms]
    change read 0 (flat 0) _ ((f 0).eval x)
    refine (congrArg (fun s => read 0 (flat 0) s ((f 0).eval x)) ?_).mpr (hr 0)
    funext v
    rfl
  | succ n ih =>
    intro j
    let sub := fun i => flat (copyIndex k n (j,i))
    let prior := fun i => pr (copyIndex k n (j,i))
    let nested := nestedPrivatePrograms (fun z => (view 0 z).pack) (n+1) flat pr
    have eq : privateChild (leavesEquiv k _ (n+1) flat) nested j =
        nestedPrivatePrograms (fun z => (view 0 z).pack) n sub prior := subInitial_nested view n flat pr j
    change PrivateLeaves read x n (leavesEquiv k _ n sub) (privateChild (leavesEquiv k _ (n+1) flat) nested j) _
    rw [eq]
    exact ih sub prior (fun i => f (copyIndex k n (j,i))) (fun i => hr _)

/-- The flat physical gate list on the encoded local histograms has the
readback property of the exact recursively saved private programs. -/
theorem private_flat_output
    (next : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
      (pr : ∀ j, Site.Programs (view i.val (c j)).pack.layout) (y : Fin k → W i.val → Bool),
      (∀ j, read i.val (c j) (pr j) (y j)) →
      read (i.val+1) (F.advance i c q) (F.savePrivatePrograms store rows number i c q pr)
        (fun z => (step i.val i.isLt).eval (Sum.elim (fun t => y t.1 t.2) (codec.word i.val i.isLt c q)) (.inl z)))
    (flat : Fin (k^b) → A 0) (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (y : Fin (k^b) × W 0 → Bool) (leaf : ∀ i, read 0 (flat i) (pr i) (fun z => y (i,z))) (q : F.Hist flat) :
    let nested := nestedPrivatePrograms (fun z => (view 0 z).pack) b flat pr
    let root := F.replayPrivatePrograms store rows number b le_rfl (leavesEquiv k _ b flat) nested q
    read b ((flatChoice F.system flat).term q) root
      (fun z => (flatEpoch step).eval (Sum.elim y (flatWord codec flat q)) (.inl z)) := by
  intro nested root
  let leafF (i : Fin (k^b)) : Frame (Fin (k^b) × W 0) (W 0) := Frame.initial fun z => (i,z)
  have readF (i) : (leafF i).eval y = fun z => y (i,z) := funext (Frame.initial_eval _ _)
  have hl := flat_leaves read y b flat pr leafF (fun i => (readF i).symm ▸ leaf i)
  exact F.private_output store rows number codec step read y next b le_rfl (leavesEquiv k _ b flat)
    nested (leavesEquiv k _ b leafF) hl q

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
