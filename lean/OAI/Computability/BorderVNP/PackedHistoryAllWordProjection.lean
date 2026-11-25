import OAI.Computability.BorderVNP.PackedHistoryEpoch
import OAI.Computability.BorderVNP.PackedHistoryOuter

/-! # Projections of compiled history frames on all input and guess words

The retained state and the subtree validity bit agree even when a local
profile or an earlier child's profile fails its guard.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Packing VPVNP.VerifierNetwork
open private leafFrames from OAI.Computability.BorderVNP.PackedHistoryEpoch

variable {k b : ℕ} {W V G : ℕ → Type}
    [∀ j, Fintype (W j)] [∀ j, Fintype (V j)] [∀ j, Fintype (G j)]

/-- Every local state projection commutes with the retained word and the validity
wire on arbitrary child states and arbitrary local profile guesses. -/
def StepsProject (pick : ∀ j, V j → W j) (aug : Steps k b W G) (plain : Steps k b V G) : Prop :=
  ∀ j hj (x : LocalPins k (W j) (G j) → Bool) (r : Result (V (j+1))),
    (aug j hj).eval x (Sum.map (pick (j+1)) id r) =
      (plain j hj).eval (x ∘ Sum.map (Prod.map id (pick j)) id) r

/-- Correspondence of two arrays of leaf frames in the original row-major tree. -/
def LeavesProject {U Z : Type*} (rel : U → Z → Prop) : (n : ℕ) → Leaves k U n → Leaves k Z n → Prop
  | 0, u, z => rel u z
  | n+1, u, z => ∀ i, LeavesProject rel n (u i) (z i)

variable {σ τ : Type*} [Fintype σ] [Fintype τ]
    {pick : ∀ j, V j → W j} {aug : Steps k b W G} {plain : Steps k b V G}

/-- The retained output and the physical validity bit of the entire tree
are preserved on every choice string, including malformed ones. The two
initial frames can read different input domains. -/
theorem StepsProject.tree (project : StepsProject pick aug plain) (n : ℕ) (hn : n ≤ b)
    (fs : Leaves k (Frame σ (W 0)) n) (gs : Leaves k (Frame τ (V 0)) n)
    (x : σ → Bool) (y : τ → Bool)
    (leaves : LeavesProject (fun (f : Frame σ (W 0)) (h : Frame τ (V 0)) => f.eval x ∘ pick 0 = h.eval y) n fs gs)
    (g : Slot k G n → Bool) :
    output aug n hn fs x g ∘ pick n = output plain n hn gs y g ∧
      flag aug n hn fs x g = flag plain n hn gs y g := by
  induction n with
  | zero =>
    have initial : (fs : Frame σ (W 0)).eval x ∘ pick 0 = (gs : Frame τ (V 0)).eval y := leaves
    exact ⟨(congrArg (fun f => f ∘ pick 0) (output_zero aug fs x g)).trans
      (initial.trans (output_zero plain gs y g).symm), (flag_zero aug fs x g).trans (flag_zero plain gs y g).symm⟩
  | succ n ih =>
    have children (i : Fin k) := ih (by omega) (fs i) (gs i) (leaves i) (childGuess g i)
    have inputs : localInput aug n hn fs x g ∘ Sum.map (Prod.map id (pick n)) id =
        localInput plain n hn gs y g := by
      funext z
      cases z with
      | inl z => exact congrFun (children z.1).1 z.2
      | inr z => rfl
    have node (r : Result (V (n+1))) :
        (aug n hn).eval (localInput aug n hn fs x g) (Sum.map (pick (n+1)) id r) =
        (plain n hn).eval (localInput plain n hn gs y g) r :=
      (project n hn _ r).trans (congrArg (fun x => (plain n hn).eval x r) inputs)
    constructor
    · funext z
      change output aug (n+1) hn fs x g (pick (n+1) z) = output plain (n+1) hn gs y g z
      rw [output_succ, output_succ]
      exact node (.inl z)
    · apply Bool.eq_iff_iff.mpr
      rw [flag_succ, flag_succ]
      exact and_congr (forall_congr' fun i => iff_of_eq (congrArg (· = true) (children i).2))
        (iff_of_eq (congrArg (· = true) (node (.inr ()))))

/-- In the outer normalized history the same seed initializer is repeated at
every leaf. Its single pointwise input relation suffices on all profiles. -/
theorem StepsProject.repeatLeaf (project : StepsProject pick aug plain) (n : ℕ) (hn : n ≤ b)
    (f : Frame σ (W 0)) (h : Frame τ (V 0)) (x : σ → Bool) (y : τ → Bool)
    (leaf : f.eval x ∘ pick 0 = h.eval y) (g : Slot k G n → Bool) :
    output aug n hn (repeatLeaf k f n) x g ∘ pick n = output plain n hn (repeatLeaf k h n) y g ∧
      flag aug n hn (repeatLeaf k f n) x g = flag plain n hn (repeatLeaf k h n) y g := by
  apply project.tree
  clear g hn
  induction n with
  | zero => exact leaf
  | succ n ih => exact fun _ => ih

/-- Projecting a flattened epoch preserves every compiled state bit and the
flag for every original input, without a precondition on the guess word. -/
theorem StepsProject.flatEpoch (project : StepsProject pick aug plain)
    (x : LocalPins (k^b) (W 0) (Slot k G b) → Bool) (r : Result (V b)) :
    (flatEpoch aug).eval x (Sum.map (pick b) id r) =
      (flatEpoch plain).eval (x ∘ Sum.map (Prod.map id (pick 0)) id) r := by
  let xa : Fin (k^b) × W 0 → Bool := fun j => x (.inl j)
  let xp : Fin (k^b) × V 0 → Bool := fun j => xa (j.1, pick 0 j.2)
  let g : Slot k G b → Bool := fun j => x (.inr j)
  have mapped {U Z : Type} (rel : U → Z → Prop) (t : ℕ)
      (u : Fin (k^t) → U) (z : Fin (k^t) → Z) (all : ∀ i, rel (u i) (z i)) :
      LeavesProject rel t (leavesEquiv k U t u) (leavesEquiv k Z t z) := by
    induction t with
    | zero => exact all 0
    | succ t ih => exact fun i => ih (fun j => u (copyIndex k t (i,j))) (fun j => z (copyIndex k t (i,j))) (fun _ => all _)
  have leaves : LeavesProject (fun (f : Frame (Fin (k^b) × W 0) (W 0)) (h : Frame (Fin (k^b) × V 0) (V 0)) =>
      f.eval xa ∘ pick 0 = h.eval xp) b (leafFrames k b (W 0)) (leafFrames k b (V 0)) := by
    unfold leafFrames
    apply mapped
    intro i
    funext z
    exact (Frame.initial_eval _ xa (pick 0 z)).trans (Frame.initial_eval (fun v : V 0 => (i,v)) xp z).symm
  have all := project.tree b le_rfl _ _ xa xp leaves g
  have left : Sum.elim xa g = x := by funext z; cases z <;> rfl
  have right : Sum.elim xp g = x ∘ Sum.map (Prod.map id (pick 0)) id := by funext z; cases z <;> rfl
  cases r with
  | inl v =>
    have hv := congrFun all.1 v
    simpa only [Function.comp_apply, output, left, right, PackedHistoryCircuit.flatEpoch, Sum.map_inl] using hv
  | inr v =>
    cases v
    simpa only [flag, left, right, PackedHistoryCircuit.flatEpoch, Sum.map_inr, id_eq] using all.2

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
