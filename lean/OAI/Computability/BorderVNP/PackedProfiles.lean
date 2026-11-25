import OAI.Computability.BorderVNP.CrossingParallel
import OAI.Computability.BorderVNP.ShortenNetworkHistory

/-! # Adaptive epoch profiles and exterior contraction

Proposition 7.2 applies Lemma 6.1 to a tree of packs. A parent chooses profiles *after* its
children's profiles are known. The indexing below therefore keeps the dependent sum over those
choices. Its leaf count is the number of copies of the substituted network, and the final tensor
identity remains valid when its ports are attached to the original physical links and pins.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Crossing

/-- The actual free ports of a pack, retaining the copy number within each bottom bundle. -/
def PackPorts (P : Type) (b K : ℕ) : ℕ → Type
  | 0 => Fin b × P
  | t + 1 => Fin K × PackPorts P b K t

/-- Each copy retains the width of each of its original ports. -/
def packWidth {P : Type} (bits : P → ℕ) (b K : ℕ) : (t : ℕ) → PackPorts P b K t → ℕ
  | 0, p => bits p.2
  | t + 1, p => packWidth bits b K t p.2

instance {P : Type} [Fintype P] (b K : ℕ) (t : ℕ) : Fintype (PackPorts P b K t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype (Fin b × P))
  | succ t ih => exact inferInstanceAs (Fintype (Fin K × PackPorts P b K t))

/-- There are `b * K^t` original copies in the level-`t` pack. -/
theorem card_packPorts {P : Type} [Fintype P] (b K t : ℕ) :
    Fintype.card (PackPorts P b K t) = b * K^t * Fintype.card P := by
  induction t with
  | zero =>
    change Fintype.card (Fin b × P) = _
    rw [Fintype.card_prod, Fintype.card_fin, pow_zero, mul_one]
  | succ t ih =>
    change Fintype.card (Fin K × PackPorts P b K t) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]; ring

/-- A network together with its actual local entries. -/
abbrev ValuedPack (R : Type*) (D : ℕ) {P : Type} (bits : P → ℕ) :=
  Shortening.Pack D P bits R

/-- Parallel composition of the networks, also combining their local tables. -/
def parallelPacks {R : Type*} {D K : ℕ} {P : Type} {bits : P → ℕ}
    (input : Fin K → ValuedPack R D bits) : ValuedPack R D (fun p : Fin K × P => bits p.2) :=
  ⟨Network.parallel (fun i => (input i).1), Network.parallelTables _ (fun i => (input i).2)⟩

/-- The original batch with every copy kept independent, prior to any shortening. -/
def unshortened {R : Type*} {D : ℕ} {P : Type} {bits : P → ℕ}
    (original : ValuedPack R D bits) (b K : ℕ) : (t : ℕ) → ValuedPack R D (packWidth bits b K t)
  | 0 => parallelPacks (fun _ : Fin b => original)
  | t+1 => parallelPacks (fun _ : Fin K => unshortened original b K t)

/-- Finite summands of a tensor identity, with separate indices retained for equal summands. -/
structure ProfileSum (A : Type*) where
  /-- A valid choice of all profiles producing this summand. -/
  Index : Type
  /-- Enumeration of the valid choices. -/
  finite : Fintype Index
  /-- Publicly selected network, including the boxes it retains. -/
  term : Index → A

attribute [instance] ProfileSum.finite

/-- Choose the children independently, then select a parent profile from the finite set for
those exact child packs. -/
def combineProfiles {A B : Type*} {K : ℕ} (input : Fin K → ProfileSum A)
    (epoch : (Fin K → A) → ProfileSum B) : ProfileSum B where
  Index := Σ c : ∀ i, (input i).Index, (epoch (fun i => (input i).term (c i))).Index
  finite := inferInstance
  term h := (epoch (fun i => (input i).term (h.1 i))).term h.2

/-- Build the dependent history index through every epoch, retaining the final pack at each leaf. -/
def packHistory {Pack : ℕ → Type*} {K : ℕ} (bottom : Pack 0)
    (epoch : ∀ t, (Fin K → Pack t) → ProfileSum (Pack (t + 1))) :
    (t : ℕ) → ProfileSum (Pack t)
  | 0 => ⟨PUnit, inferInstance, fun _ => bottom⟩
  | t+1 => combineProfiles (fun _ => packHistory bottom epoch t) (epoch t)

section Contraction

variable {R : Type*} [CommSemiring R] {P : Type} {bits : P → ℕ} {D b K : ℕ}
variable (original : ValuedPack R D bits)
variable (epoch : ∀ t, (Fin K → ValuedPack R D (packWidth bits b K t)) →
  ProfileSum (ValuedPack R D (packWidth bits b K (t+1))))

/-- Pointwise form of the one-epoch identity in Lemma 6.1. The profile enumeration can depend
on the public configuration of the child packs. -/
def ExactEpoch : Prop :=
  ∀ t input (x : Ports (packWidth bits b K (t+1))),
    (parallelPacks input).1.value (parallelPacks input).2 x =
      ∑ j, ((epoch t input).term j).1.value ((epoch t input).term j).2 x

/-- Index the actual outputs of a sequence of cable removals, insertions and grouped profile
replacements, retaining the original multiplicities. -/
noncomputable def replacementProfiles {p : ValuedPack R D bits} (H : Shortening.History p) :
    ProfileSum (ValuedPack R D bits) where
  Index := Fin H.outputs.length
  finite := inferInstance
  term := H.outputs.get

private theorem sumGet {A R : Type*} [AddCommMonoid R] (l : List A) (f : A → R) :
    (l.map f).sum = ∑ j : Fin l.length, f (l.get j) := by
  have h := congrArg (fun xs : List A => (xs.map f).sum) (List.ofFn_get (l := l)).symm
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using h

/-- A concrete cable-replacement history at every combined pack satisfies the one-epoch
identity, including cuts of previously introduced selector cables. -/
theorem exactEpoch_of_replacements
    (select : ∀ t (child : Fin K → ValuedPack R D (packWidth bits b K t)),
      Shortening.History (parallelPacks child)) :
    ExactEpoch (fun t child => replacementProfiles (select t child)) := by
  intro t child x
  let H := select t child
  change (parallelPacks child).tensor x = ∑ j : Fin H.outputs.length, (H.outputs.get j).tensor x
  exact (H.sum_outputs x).trans (sumGet H.outputs (fun q : ValuedPack R D (packWidth bits b K (t+1)) => q.tensor x))

/-- Summing over *valid adaptive profile histories* gives the original parallel tensor. -/
theorem value_packHistory (hid : ExactEpoch epoch) (t : ℕ) (x : Ports (packWidth bits b K t)) :
    let H := packHistory (unshortened original b K 0) epoch t
    (unshortened original b K t).1.value (unshortened original b K t).2 x =
      ∑ h, (H.term h).1.value (H.term h).2 x := by
  classical
  dsimp only
  induction t with
  | zero =>
    exact (Fintype.sum_unique (fun _ : PUnit => (unshortened original b K 0).1.value
      (unshortened original b K 0).2 x)).symm
  | succ t ih =>
    let H := packHistory (unshortened original b K 0) epoch t
    rw [show (unshortened original b K (t+1)).1.value (unshortened original b K (t+1)).2 x =
      ∏ i : Fin K, (unshortened original b K t).1.value (unshortened original b K t).2
        (fun p => x (i,p)) from Network.parallel_value (fun _ : Fin K => (unshortened original b K t).1)
          (fun _ : Fin K => (unshortened original b K t).2) x]
    trans ∏ i : Fin K, ∑ h : H.Index, (H.term h).1.value (H.term h).2 (fun p => x (i,p))
    · exact Finset.prod_congr rfl fun i _ => ih (fun p => x (i,p))
    rw [Fintype.prod_sum]
    change _ = ∑ h : Σ c : Fin K → H.Index, (epoch t (fun i => H.term (c i))).Index,
      ((epoch t (fun i => H.term (h.1 i))).term h.2).1.value
        ((epoch t (fun i => H.term (h.1 i))).term h.2).2 x
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    exact (Network.parallel_value (fun i => (H.term (c i)).1)
      (fun i => (H.term (c i)).2) x).symm.trans (hid t (fun i => H.term (c i)) x)

/-- The same sum identity holds after sewing on exterior links, pins or polynomial-valued
tables. Each exterior bit is summed only once. -/
theorem value_sew_packHistory [Fintype P] (hid : ExactEpoch epoch) (t : ℕ) {Q : Type*}
    {free : Q → ℕ} (outside : Network D (Q ⊕ PackPorts P b K t)
      (Sum.elim free (packWidth bits b K t))) (outer : outside.Tables R) (x : Ports free) :
    let source := unshortened original b K t
    let H := packHistory (unshortened original b K 0) epoch t
    (outside.sew source.1).value (outside.sewTables source.1 outer source.2) x =
      ∑ h, (outside.sew (H.term h).1).value (outside.sewTables (H.term h).1 outer (H.term h).2) x :=
  Network.value_sew_sum outside outer _ _ _ _ (value_packHistory original epoch hid t) x

end Contraction

end Packing

end BorderVNP
end Computability
end OAI
