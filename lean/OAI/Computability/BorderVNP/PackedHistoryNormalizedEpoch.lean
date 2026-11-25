import OAI.Computability.BorderVNP.PackedHistoryNormalizedProjection
import OAI.Computability.BorderVNP.PackedHistoryAdapters
import OAI.Computability.BorderVNP.PackedHistoryDenseCodec
import OAI.Computability.BorderVNP.ShortenDenseExecution

/-! # Compiled count words of the normalized site execution

The native output ordinal enumerates a dense physical history. Projecting
the verifier states onto that machine identifies the same local choices,
in the same tree order, and the same densely stored terminal network.
The surrounding frames subdivide the actual inputs and place this root
on the sites of the specified execution.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Epoch.Round Cover Shortening Packing Catalog Adaptive Physical VPVNP.VerifierNetwork
open scoped Classical
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}

namespace Program

variable {k b : ℕ} {I P : Type} [Fintype I] {bits : P → ℕ} {A : ℕ → Type*}
    {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Normalized.Program (B := B) e view)
    (good : ∀ j, A j → Prop) (closed : Capacity.Closed F.system good)

/-- Use the genuine dense-input program on physically admissible states.
The sorted stage and its profile on every such child tuple are unchanged. -/
noncomputable def restrict : Normalized.Program (B := B) e
    (fun n (a : {a // good n a}) => view n a.val) where
  stage i c := F.stage i (Subtype.val ∘ c)
  advance i c q := ⟨F.advance i (Subtype.val ∘ c) q,closed i.val i.isLt _ (fun a => (c a).property) q⟩
  sound i c q := F.sound i (Subtype.val ∘ c) q

/-- The normalized bounded codec acts on the exact adaptive restriction. -/
theorem restrict_system : (F.restrict good closed).system = Capacity.restrict F.system good closed := rfl

end Program

namespace SiteExecution

variable {S : SiteSchedule e} {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {M : SiteMachine S d P bits} {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
    {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget} (run : SiteExecution S M input route)
    {A : ℕ → Type*} {R : System S.fanIn S.rounds A} (p : Projection R M.F.system)
    (leaf : Fin (S.fanIn^S.rounds) → A 0) (hleaf : ∀ i, p.physical 0 (leaf i) = run.flat i)

/-- Native output number of the dense epoch as the exact recursive history
of its verifier state. The correspondence at each node is supplied by the projection. -/
noncomputable def ordinal : Fin run.expansion.terms ≃ (flatChoice R leaf).Index :=
  run.enum.trans (p.flat leaf run.flat hleaf).index.symm

/-- The final network is exactly the stored physical network for this numbered
term, including its layout, tensor tables, site placement and charged segments. -/
theorem ordinal_root (q : Fin run.expansion.terms) :
    (p.physical S.rounds ((flatChoice R leaf).term (run.ordinal p leaf hleaf q))).val =
      M.F.terminal run.flat (run.enum q) := by
  let corr := p.flat leaf run.flat hleaf
  have h := corr.root (corr.index.symm (run.enum q))
  rw [corr.index.apply_symm_apply] at h
  exact congrArg Subtype.val h

/-- Actual fixed count fields of all branches in this physical output ordinal. -/
noncomputable def word {G : ℕ → Type} (C : Codec R G) (q : Fin run.expansion.terms) :
    Slot S.fanIn G S.rounds → Bool :=
  flatWord C leaf (run.ordinal p leaf hleaf q)

/-- Distinct native ordinals have distinct full profile words. -/
theorem word_injective {G : ℕ → Type} (C : Codec R G) :
    Function.Injective (run.word p leaf hleaf C) :=
  (flatWord_injective C leaf).comp (run.ordinal p leaf hleaf).injective

/-- The wrapped epoch accepts exactly these native count words. Its public
state represents the actual returned pack and integral site routes of that
same ordinal, after the supplied physical input and terminal transformations. -/
theorem correct {G W : ℕ → Type} [∀ i, Fintype (G i)] [∀ i, Fintype (W i)] {X V : Type}
    [Fintype X] [Fintype V] (C : Codec R G) (rep : Represents A W) (step : Steps S.fanIn S.rounds W G)
    (ok : LocalCorrect C rep step) (pre : Frame X (Fin (S.fanIn^S.rounds) × W 0))
    (post : Frame (X ⊕ W S.rounds) V) (x : X → Bool)
    (result : (V → Bool) → (pack : Pack D (Fin (S.fanIn^S.rounds) × P) (fun z => bits z.2) K) →
      SiteRoutes pack (Cube D) (d+1) S.budget → Prop)
    (start : ∀ i, rep 0 (fun j => pre.eval x (i,j)) (leaf i))
    (finish : ∀ (i : M.F.Hist run.flat) z a, rep S.rounds z a →
      (p.physical S.rounds a).val = M.F.terminal run.flat i →
      result (post.eval (Sum.elim x z)) (flattenPack S.rounds (M.F.terminal run.flat i).pack)
        (run.out i).routes.flatten)
    (g : Slot S.fanIn G S.rounds → Bool) :
    let f := wrappedEpoch pre step post
    (f.eval (Sum.elim x g) (.inr ()) = true ↔ ∃ q, g = run.word p leaf hleaf C q) ∧
    ∀ q, g = run.word p leaf hleaf C q →
      result (fun j => f.eval (Sum.elim x g) (.inl j)) (run.expansion.pack q) (run.expansion.routes q) := by
  intro f
  let idx := run.ordinal p leaf hleaf
  have tree := flatEpoch_correct C rep step ok leaf (fun i j => pre.eval x (i,j)) start g
  constructor
  · rw [show f.eval (Sum.elim x g) (.inr ()) = _ from wrappedEpoch_flag pre step post x g,tree.1]
    constructor
    · rintro ⟨a,ha⟩
      refine ⟨idx.symm a,?_⟩
      change g = flatWord C leaf (idx (idx.symm a))
      rwa [idx.apply_symm_apply]
    · rintro ⟨q,hq⟩
      exact ⟨idx q,hq⟩
  · intro q hq
    rw [show (fun j => f.eval (Sum.elim x g) (.inl j)) = _ from wrappedEpoch_state pre step post x g]
    exact finish (run.enum q) _ _ (tree.2 (idx q) hq) (run.ordinal_root p leaf hleaf q)

variable (good : ∀ j, S.State d P bits j → Prop) (closed : Capacity.Closed M.F.system good)
    (bounded : ∀ i, good 0 (run.flat i)) {w : ℕ → ℕ}

/-- Canonical count word for the actual dense execution when only admissible
physical children satisfy the public count capacity. -/
noncomputable def boundedWord (room : (M.F.restrict good closed).Fits w) (q : Fin run.expansion.terms) :=
  run.word (Projection.capacity M.F.system good closed) (fun i => ⟨run.flat i,bounded i⟩) (fun _ => rfl)
    ((M.F.restrict good closed).codec room) q

/-- The bounded public count words still distinguish all original dense ordinals. -/
theorem boundedWord_injective (room : (M.F.restrict good closed).Fits w) :
    Function.Injective (run.boundedWord good closed bounded room) :=
  run.word_injective (Projection.capacity M.F.system good closed) _ _ ((M.F.restrict good closed).codec room)

end SiteExecution
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
