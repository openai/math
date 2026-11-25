import OAI.Computability.BorderVNP.ShortenCanonicalChart
import OAI.Computability.BorderVNP.ShortenCombiningStep

/-!
# Slotwise canonical placement for a real combined pack

Oriented segment data record the two actual endpoints in the chart of their
midpoint tile. Sorted pooling can only select old segments whose direction
bin is the indicated signed permutation of the seed. The canonical
representative therefore gives the required terminal tolerance for every
slot, with each tile projecting its own local lift to the quotient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.CanonicalPlacement

open Epoch Crossing SeedIntervals CombiningStep Set
open scoped Classical

variable {D : ℕ} {T S : Type} {window : Set (HyperbolicHost (Cube D))} {η : ℝ}

/-- A single oriented segment in the tile coordinates that are actually tested. -/
structure Segment (T S : Type) (window : Set (HyperbolicHost (Cube D))) where
  /-- Actual midpoint tile, after any post-translation. -/
  tile : T
  /-- Relative length/speed class of this segment. -/
  kind : S
  /-- The midpoint represented in the tie-resolved base tile. -/
  center : HyperbolicHost (Cube D)
  /-- Product unit tangent at the represented midpoint. -/
  direction : Direction D ℂ
  /-- The center lies in the compact window used to construct the relative bins. -/
  mem : center ∈ window
  /-- The oriented tangent has unit product norm. -/
  norm : ‖direction‖ = 1

variable (r : S → ℝ) (C : ∀ s, BinChart D window (r s) η)

/-- The product-tile address followed by the relative class and its bin. -/
abbrev Address (T : Type) := T × (Σ s, Fin (C s).bins)

/-- Determine the public bin of an oriented cable. -/
def address (y : Segment T S window) : Address r C T :=
  (y.tile,⟨y.kind,(C y.kind).code (y.center,y.direction)⟩)

/-- The direction permutations act solely on the relative bin. -/
def perm (j : Fin D) : Equiv.Perm (Address r C T) :=
  (Equiv.refl T).prodCongr (Equiv.sigmaCongrRight (fun s => (C s).perm j))

/-- Every seed in a tile uses the corresponding canonical representative. -/
noncomputable def chart (a : Address r C T) : SeedChart (Cube D) D :=
  (C a.2.1).seed a.2.2

/-- A classified segment in the appropriate signed bin can attach both of its terminals. -/
theorem hook_bound (a : Address r C T) (j : Fin D) (y : Segment T S window)
    (hy : address r C y = perm r C j a) (neg : Bool) :
    dist (endpoint y.center y.direction (r y.kind) neg) ((chart r C a).atTerminal (j,neg)) ≤
      η * (chart r C a).radius := by
  rcases a with ⟨t,s,b⟩
  rcases y with ⟨t',s',c,v,hc,hv⟩
  change ((t', ⟨s',(C s').code (c,v)⟩) : Address r C T) = (t,⟨s,(C s).perm j b⟩) at hy
  have hkind := congrArg (fun a : Address r C T => a.2.1) hy
  change s' = s at hkind
  subst s'
  have hcode := Sigma.mk.inj_iff.mp (congrArg Prod.snd hy)
  change dist (endpoint c v (r s) neg) ((C s).seed b |>.atTerminal (j,neg)) ≤ η * r s
  rw [BinChart.terminal_eq]
  exact (C s).close b j c hc v hv (eq_of_heq hcode.2) neg

variable {P : Type*} {bits : P → ℕ} {K Q : Type*} [PseudoMetricSpace Q] {m : ℕ} [NeZero D]
    (p : Pack D P bits K) (data : p.layout.Edge → Option (Segment T S window))

/-- Inactive cables have no bin and travel intact with their pack. -/
def bin (e : p.layout.Edge) : Option (Address r C T) := (data e).map (address r C)

private theorem selected_data {a : Address r C T}
    (e : ↥((partition p.layout (bin r C p data) (perm r C) m).part a)) :
    ∃ y, data e.val.1 = some y ∧ address r C y = perm r C (direction e.val.2) a := by
  have h := bin_selected p.layout (bin r C p data) (perm r C) m e
  unfold bin at h
  cases he : data e.val.1 with
  | none => simp [he] at h
  | some y => exact ⟨y,rfl,Option.some.inj (by simpa only [he,Option.map_some] using h)⟩

variable [Fintype T] [Fintype S] (old : p.layout.Site → Q)
    (π : T → HyperbolicHost (Cube D) → Q) (nonexpanding : ∀ t u v, dist (π t u) (π t v) ≤ dist u v)

/-- A lifted description realizes both signed slots at their actual quotient sites. -/
structure Realizes : Prop where
  /-- The negative endpoint is the old source slot. -/
  src : ∀ c y, data c = some y → π y.tile (endpoint y.center y.direction (r y.kind) true) = old (p.layout.src c)
  /-- The positive endpoint is the old destination slot. -/
  dst : ∀ c y, data c = some y → π y.tile (endpoint y.center y.direction (r y.kind) false) = old (p.layout.dst c)
  /-- The short segment projects isometrically in its ball. -/
  length : ∀ c y, data c = some y → dist (old (p.layout.src c)) (old (p.layout.dst c)) = 2*r y.kind

variable (realized : Realizes r p data old π)

omit [Fintype T] [Fintype S] in
include nonexpanding realized in
/-- Build the physical placement and the fits certificate together, using
the real interval partition and both endpoint slots of each selected edge. -/
theorem exists_placement {h ν : ℝ} (hr : ∀ s, r s ∈ Icc (0:ℝ) h) (hη : η ≤ ν/4) :
    ∃ g : Placement (m := m) p (bin r C p data) (perm r C) (Cube D) Q,
      g.old = old ∧ g.chart = chart r C ∧ g.project = (fun a => π a.1) ∧
      g.fits p (bin r C p data) (perm r C) (fun _ => true) h ν := by
  let pick {a} (e : ↥((partition p.layout (bin r C p data) (perm r C) m).part a)) :=
    (selected_data r C p data e).choose
  have spec {a} (e : ↥((partition p.layout (bin r C p data) (perm r C) m).part a)) :
      data e.val.1 = some (pick e) ∧ address r C (pick e) = perm r C (direction e.val.2) a :=
    (selected_data r C p data e).choose_spec
  let lift (a : Address r C T) : (layout p.layout (bin r C p data) (perm r C) m).CutPorts
      ((partition p.layout (bin r C p data) (perm r C) m).part a) → HyperbolicHost (Cube D) :=
    Sum.elim (fun e => endpoint (pick e).center (pick e).direction (r (pick e).kind) true)
      (fun e => endpoint (pick e).center (pick e).direction (r (pick e).kind) false)
  refine ⟨{
    old := old
    chart := chart r C
    project := fun a => π a.1
    lift := lift
    nonexpanding := fun a => nonexpanding a.1
    projects := ?_
    bin_length := ?_
    invariant := ?_
  },rfl,rfl,rfl,?_⟩
  · intro a q
    cases q with
    | inl e =>
      have ht : (pick e).tile = a.1 := congrArg Prod.fst (spec e).2
      exact ht ▸ realized.src _ _ (spec e).1
    | inr e =>
      have ht : (pick e).tile = a.1 := congrArg Prod.fst (spec e).2
      exact ht ▸ realized.dst _ _ (spec e).1
  · intro e a hbin
    unfold bin at hbin
    cases he : data e with
    | none => simp [he] at hbin
    | some y =>
      have ha : address r C y = a := Option.some.inj (by simpa only [he,Option.map_some] using hbin)
      subst a
      exact realized.length _ _ he
  · intro j a; rfl
  · refine ⟨fun a => hr a.2.1,?_⟩
    intro a q
    cases q with
    | inl e =>
      exact (hook_bound r C a _ (pick e) (spec e).2 true).trans (mul_le_mul_of_nonneg_right hη (hr a.2.1).1)
    | inr e =>
      exact (hook_bound r C a _ (pick e) (spec e).2 false).trans (mul_le_mul_of_nonneg_right hη (hr a.2.1).1)

end Shortening.CanonicalPlacement

end BorderVNP
end Computability
end OAI
