import OAI.Computability.BorderVNP.PackedHistoryDenseCodec
import OAI.Computability.BorderVNP.PackedHistoryDenseReady

/-! # Canonical physical state of the shared shortening traversal

At a given node the program can examine only the bits stored by its child
frames. The semantic state therefore retains all of those assigned bits, the
actual sparse row names of its pack, and the accompanying local records.
This makes a motion tie depend on the same concrete arrays in the circuit
and in the tensor history, including values in unused payload positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Packing Shortening Shortening.Adaptive Epoch Physical VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

/-- A placed pack, the actual sparse names used to read it, all assigned public
pins, and the per-node metadata needed for its local site computations. -/
structure NamedState (D : ℕ) (P : Type) (bits : P → ℕ) (K : Type*) (lev V E : ℕ)
    (Pins : Type) (Payload : Type*) where
  /-- Actual layout and field tables at this node. -/
  placed : PlacedPack D P bits K (Cube D) lev
  /-- The stable rows, including the site of each padded cable slot. -/
  names : Directory placed V E
  /-- The entire bit assignment emitted by the shared program. -/
  words : Pins → Bool
  /-- Retained local computation and any further site data. -/
  payload : Payload

namespace NamedState

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {lev V E : ℕ → ℕ} {W : ℕ → Type} {Extra : ℕ → Type*}
    {B : Fin b → Type} [∀ i, Fintype (B i)] [∀ j, Fintype (W j)]
    {w : ℕ → ℕ} (e : PaidIdentity K D m)

/-- An arbitrary level of the named public history. -/
abbrev At (j : ℕ) := NamedState D (Port k P j) (width bits k j) K (lev j) (V j) (E j) (W j) (Extra j)

variable {good : ∀ j, At (D := D) (K := K) (lev := lev) (V := V) (E := E)
    (W := W) (Extra := Extra) (k := k) (bits := bits) j → Prop}

/-- Admissible stored rows. An invariant is imposed only on states used in the physical traversal. -/
abbrev Admissible (good : ∀ j, At (D := D) (K := K) (lev := lev) (V := V) (E := E)
    (W := W) (Extra := Extra) (k := k) (bits := bits) j → Prop) (j : ℕ) := {x // good j x}

variable (stage : ∀ (i : Fin b) (c : Fin k → Admissible good i.val),
    Stage m (B i) (lev (i.val+1)) (fun j => (c j).val.placed))
    (room : ∀ i c a, (stage i c).matched a < 2^w i.val)
    (kernel : Steps k b W (Pin (Cube D) B lev e.count w))
    (names : ∀ i c (hist : (stage i c).Index e),
      Directory ((stage i c).result e hist) (V (i.val+1)) (E (i.val+1)))
    (extra : ∀ i c, (stage i c).Index e → Extra (i.val+1))

/-- Exact input guess assignment of one selected physical histogram. -/
noncomputable def guess (i : Fin b) (c : Fin k → Admissible good i.val) (hist : (stage i c).Index e) :
    Pin (Cube D) B lev e.count w i.val → Bool :=
  (fields (I := Cube D) (B := B) (depth := lev) (e := e) w i).symm
    ((BankCircuit.branches e (stage i c).matched (room i c)).symm hist).val

/-- Evaluate the actual kernel on the child pin assignments, and save the resulting
array together with the physical network and sparse names on that histogram. -/
noncomputable def save (i : Fin b) (c : Fin k → Admissible good i.val) (hist : (stage i c).Index e) :
    At (D := D) (K := K) (lev := lev) (V := V) (E := E) (W := W) (Extra := Extra)
      (k := k) (bits := bits) (i.val+1) :=
  let d := names i c hist
  let x := Sum.elim (fun p : Fin k × W i.val => (c p.1).val.words p.2) (guess e stage room i c hist)
  ⟨((stage i c).result e hist).dense d.cables,d.dense,(kernel i.val i.isLt).eval x ∘ Sum.inl,extra i c hist⟩

/-- The saved pin array is the actual output of this kernel evaluation at the child
arrays and histogram bits. A consumer may read any of its indices, including padding. -/
theorem save_words (i : Fin b) (c : Fin k → Admissible good i.val) (hist : (stage i c).Index e) :
    (save e stage room kernel names extra i c hist).words =
      (kernel i.val i.isLt).eval (Sum.elim (fun p : Fin k × W i.val => (c p.1).val.words p.2)
        (guess e stage room i c hist)) ∘ Sum.inl := rfl

/-- The saved site injection is exactly the site injection computed on this branch. -/
theorem save_sites (i : Fin b) (c : Fin k → Admissible good i.val) (hist : (stage i c).Index e) :
    (save e stage room kernel names extra i c hist).names.sites = (names i c hist).sites := rfl

variable (closed : ∀ i c q, good (i.val+1) (save e stage room kernel names extra i c q))

/-- The admissible normalized program that advances the same assigned words as the circuit.
Its sole closure requirement concerns the exact output just computed at this histogram. -/
noncomputable def program : Normalized.Program (B := B) e
    (fun n (x : Admissible good n) => x.val.placed) where
  stage := stage
  advance i c q := ⟨save e stage room kernel names extra i c q,closed i c q⟩
  sound i c q :=
    let s := (stage i c).result e q
    let d := names i c q
    ⟨s.dense_tensor d.cables,s.dense_length d.cables,s.dense_concentration d.cables⟩

/-- Every actual physical histogram of the named program fits the supplied word widths. -/
theorem fits : (program e stage room kernel names extra closed).Fits w := room

/-- Equality to the actual stored pin vector enforces every payload bit,
including the unspecified entries of the sparse mathematical row relation. -/
def represents : Represents (Admissible good) W := fun _ y x => y = x.val.words

/-- Once the actual occupied reconstruction kernel checks the profile counts on these
named admissible inputs, its successor semantics on the full assigned state is exact by
construction. In particular this does not require deterministic motion selection on any
other representative of the same physical pack. -/
theorem correct (guards : ∀ (i : Fin b) (c : Fin k → Admissible good i.val)
    (g : Pin (Cube D) B lev e.count w i.val → Bool),
    ((kernel i.val i.isLt).eval (Sum.elim (fun p : Fin k × W i.val => (c p.1).val.words p.2) g) (.inr ()) = true
      ↔ BankCircuit.Accepted e (stage i c).matched (fields (e := e) w i g))) :
    let F := program e stage room kernel names extra closed
    LocalCorrect (F.codec (fits e stage room kernel names extra closed)) (represents (good := good)) kernel := by
  let F := program e stage room kernel names extra closed
  let hF : F.Fits w := room
  constructor
  · intro j hj c y g hy
    have he : y = fun a => (c a).val.words := funext hy
    subst y
    exact (guards ⟨j,hj⟩ c g).trans (F.word_image hF ⟨j,hj⟩ c g).symm
  · intro j hj c y g q hy hq
    have he : y = fun a => (c a).val.words := funext hy
    subst y
    subst g
    rfl

end NamedState
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
