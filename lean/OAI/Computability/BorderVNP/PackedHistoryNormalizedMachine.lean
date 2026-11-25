import OAI.Computability.BorderVNP.PackedHistoryNormalizedOuter

/-! # Exact profile transcripts of repeated enriched site epochs

Every node runs the fixed circuit for its outer level on the actual arrays
of its children. Accepted words name precisely the dependent histories of
this machine and preserve its complete returned state, including padding.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Catalog Adaptive PublicCapacity VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W : ℕ → Type}
    [∀ t, Fintype (W t)] (deep : S.floor+1+S.drop*T ≤ start)
    (good : ∀ t, State S start P bits shape W t → Prop)
    (V : ℕ → ℕ → Type) [∀ t i, Fintype (V t i)] (w : ℕ → ℕ → ℕ)

/-- The fixed public node program and its compiled physical frames at each
active outer depth, before the child states or their histograms are chosen. -/
abbrev Machine := ∀ t (ht : t<T), Epoch deep ht good (V t) (w t)

namespace Machine

variable {deep good V w} (M : Machine deep good V w)

/-- The exact native finite branching system, including the actual returned arrays. -/
noncomputable def system : System (fan S) T (Admissible good) :=
  ⟨fun t ht c => (M t ht).choice c⟩

/-- The same choice as an epoch family for the repeated physical pack history. -/
noncomputable def epoch (t : ℕ) (c : Fin (fan S) → Admissible good t) : ProfileSum (Admissible good (t+1)) :=
  if ht : t<T then (M t ht).choice c else ⟨Empty,inferInstance,Empty.elim⟩

/-- The two outer-history presentations use the same native local enumeration. -/
theorem system_eq : M.system = outerSystem T M.epoch := by
  unfold system outerSystem
  congr 1
  funext t ht c
  rw [epoch,dite_eq_left ht]

/-- Fixed guess pins of one full inner count tree at each outer node. -/
abbrev Guess (S : SiteSchedule e) (start : ℕ) (w : ℕ → ℕ → ℕ) (t : ℕ) :=
  Slot S.fanIn (Count S start t (w t)) S.rounds

/-- Encode each native outer choice by the canonical inner histogram count fields. -/
noncomputable def codec : Codec M.system (Guess S start w) where
  word t ht c := ((M t ht).run c).word (M t ht).room
  injective t ht c := ((M t ht).run c).word_injective (M t ht).room

/-- One copy of each level's actual subdivision, inner traversal and terminal placement. -/
noncomputable def steps : Steps (fan S) T W (Guess S start w) :=
  fun t ht => wrappedEpoch (M t ht).pre (M t ht).step (M t ht).post

/-- Every represented outer state carries exactly the complete bit vector produced at that node. -/
def represents : Represents (Admissible good) W := fun _ z a => z = a.val.words

/-- Each accepted outer word returns the actual post-frame assignment on the
enriched terminal state of that same physical branch. -/
theorem correct : LocalCorrect (A := Admissible good) (W := W) (G := Guess S start w)
    (k := fan S) (b := T) (S := M.system) M.codec (represents (good := good)) M.steps := by
  constructor
  · intro t ht c y g hy
    have h : y = fun i => (c i).val.words := funext hy
    subst y
    let E := M t ht
    change (wrappedEpoch E.pre E.step E.post).eval (Sum.elim (childWords c) g) (.inr ()) = true ↔
      ∃ q, g = (E.run c).word E.room q
    rw [wrappedEpoch_flag]
    exact (flatEpoch_correct (G := Count S start t (w t)) (W := V t) (E.F.codec E.room)
      (fun j z a => z = E.pins j a) E.step E.checked (E.run c).flat
      (fun i j => E.pre.eval (childWords c) (i,j)) (E.initial c) g).1
  · intro t ht c y g q hy hg
    have h : y = fun i => (c i).val.words := funext hy
    subst y
    let E := M t ht
    change g = (E.run c).word E.room q at hg
    change (fun j => (wrappedEpoch E.pre E.step E.post).eval (Sum.elim (childWords c) g) (.inl j)) =
      E.post.eval (Sum.elim (childWords c) (E.pins S.rounds ((E.run c).root q)))
    have hroot := (flatEpoch_correct (G := Count S start t (w t)) (W := V t) (E.F.codec E.room)
      (fun j z a => z = E.pins j a) E.step E.checked (E.run c).flat
      (fun i j => E.pre.eval (childWords c) (i,j)) (E.initial c) g).2 q hg
    exact (wrappedEpoch_state E.pre E.step E.post (childWords c) g).trans
      (congrArg (fun z => E.post.eval (Sum.elim (childWords c) z)) hroot)

/-- The checked native choice system preserves every external tensor entry at each level. -/
theorem exact : M.system.Exact (fun _ a => a.val.pack) :=
  fun t ht c x => (M t ht).epochTensor c x

/-- All genuine profiles on arbitrary inputs reproduce their full parallel
tensor, flattened back onto the row-major exterior port names. -/
theorem flat_tensor (n : ℕ) (hn : n ≤ T) (flat : Fin ((fan S)^n) → Admissible good 0)
    (x : Ports (fun z : Fin ((fan S)^n) × P => bits z.2)) :
    (parallelPacks (fun i => (flat i).val.pack)).tensor x =
      ∑ q, (flattenPack n ((state (S := M.system) n hn (leavesEquiv (fan S) _ n flat) q).val.pack)).tensor x :=
  M.system.tensor_flatHistories (fun _ a => a.val.pack) M.exact n hn flat x

omit [Fintype P] [∀ t, Fintype (W t)] in
private theorem flat_repeat (a : Admissible good 0) (n : ℕ) :
    leavesEquiv (fan S) _ n (fun _ => a) = repeatLeaf (fan S) a n := by
  induction n with
  | zero => rfl
  | succ n ih => exact funext fun _ => ih

/-- The public packing history on repeated bottom inputs has the same physical
tensor sum on its exact native terminals, with every branch multiplicity. -/
theorem repeated_tensor (bottom : Admissible good 0) (n : ℕ) (hn : n ≤ T)
    (x : Ports (fun z : Fin ((fan S)^n) × P => bits z.2)) :
    (parallelPacks (fun _ : Fin ((fan S)^n) => bottom.val.pack)).tensor x =
      ∑ q, (flattenPack n ((packHistory bottom M.epoch n).term q).val.pack).tensor x := by
  have h := M.flat_tensor n hn (fun _ => bottom) x
  rw [flat_repeat bottom n,M.system_eq] at h
  let E := outerEquiv bottom M.epoch n hn
  let f (q : (packHistory bottom M.epoch n).Index) :=
    (flattenPack n ((packHistory bottom M.epoch n).term q).val.pack).tensor x
  apply h.trans
  exact (Finset.sum_congr rfl (fun q _ => congrArg (fun a : Admissible good n => (flattenPack n a.val.pack).tensor x)
    (outerEquiv_state bottom M.epoch n hn q).symm)).trans (E.sum_comp f)

end Machine
end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
