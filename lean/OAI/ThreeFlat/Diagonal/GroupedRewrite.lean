import OAI.ThreeFlat.Diagonal.GroupedPortKernel
import OAI.ThreeFlat.Diagonal.HistoryContraction

namespace OAI
/-! # A physical history step produced by simultaneous port motif substitution

The successor graph has one edge per actual crossing motif wire. At its
site, the kernel reads only the two sorts of coordinates carried by the
history interface, the old half-wires placed there and the new half-wires
at the ends of its incident edges.
-/

namespace ThreeFlat.Diagonal.MotifKernel

open LinearAlgebra.SpectralBooks HistoryContraction
open scoped BigOperators Classical

variable {M J E G : Type} [Fintype M] [Fintype J] [Fintype E] [Fintype G] [DecidableEq G]
variable (P : M → PortGraph J E) (p : M → J → G)

abbrev Cross (m : M) := {e : E // wireOwner (P m).tail (P m).head (p m) e = none}

abbrev crossGraph : PortGraph G (Σ m, Cross P p m) :=
  ⟨fun e => p e.1 ((P e.1).tail e.2), fun e => p e.1 ((P e.1).head e.2)⟩

variable (I : M → E → Type) [∀ m e, Fintype (I m e)] [∀ m e, Inhabited (I m e)]

abbrev crossShape : Shape where
  Site := G
  Edge := Σ m, Cross P p m
  graph := crossGraph P p
  Label := fun e => I e.1 e.2

/-- Complete the incident half-wire values at `g` by arbitrary fillers on
all other edges. An endpoint table sees the coordinate taken at its own site. -/
def visible (g : G) (y : (crossShape P p I).Half g) (m : M) :
    WiresAt (P m).tail (P m).head (p m) (I := I m) none := fun e =>
  if h : p m ((P m).tail e) = g then y ⟨(⟨m,e⟩,false),h⟩
  else if h : p m ((P m).head e) = g then y ⟨(⟨m,e⟩,true),h⟩
  else default

omit [Fintype J] in
private theorem visible_eq (z : (crossShape P p I).Boundary) (m : M) (g : G) (e : Cross P p m)
    (inc : p m ((P m).tail e) = g ∨ p m ((P m).head e) = g) :
    visible P p I g ((crossGraph P p).atVertex (A := fun e => I e.1 e.2) z g) m e = z ⟨m,e⟩ := by
  unfold visible
  split_ifs with h₁ h₂ <;> first | rfl | exact False.elim (inc.elim h₁ h₂)

omit [Fintype J] in
private theorem atParty_visible (z : (crossShape P p I).Boundary) (m : M) (j : J)
    (a : WiresAt (P m).tail (P m).head (p m) (I := I m) (some (p m j))) :
    atParty (P m).tail (P m).head (p m) j
      (visible P p I (p m j) ((crossGraph P p).atVertex (A := fun e => I e.1 e.2) z (p m j)) m) a =
    atParty (P m).tail (P m).head (p m) j (fun e => z ⟨m,e⟩) a := by
  apply Prod.ext <;> funext e he <;> subst j <;>
    by_cases hi : p m ((P m).tail e) = p m ((P m).head e) <;> simp only [atParty,hi,↓reduceDIte]
  · apply visible_eq; exact Or.inl rfl
  · apply visible_eq; exact Or.inr rfl

private theorem sum_congr_instances {α K : Type*} [AddCommMonoid K] (U V : Fintype α)
    (f g : α→K) (same : ∀ a,f a=g a) :
    (@Finset.univ α U).sum f=(@Finset.univ α V).sum g := by
  cases Subsingleton.elim U V
  exact Finset.sum_congr rfl (fun a _=>same a)

/-- The full product of motif kernels agrees with a contraction over the
physical graph of all surviving wires. -/
theorem cross_contract {F : Type*} [CommSemiring F] (K : ∀ m j, (P m).State (I m) j → F) :
    (crossShape P p I).contract (fun g y => ∏ m, groupedFactor (P m) (p m) (K m) g (visible P p I g y m)) =
    ∑ b : ∀ m, WiresAt (P m).tail (P m).head (p m) (I := I m) none,
      ∏ g, ∏ m, groupedFactor (P m) (p m) (K m) g (b m) := by
  let eqv : (crossShape P p I).Boundary ≃ (∀ m, WiresAt (P m).tail (P m).head (p m) (I := I m) none) :=
    Equiv.piCurry (fun (m : M) (e : Cross P p m) => I m e.val)
  rw [← eqv.sum_comp]
  unfold Shape.contract PortGraph.contraction
  apply Finset.sum_congr (by ext a; simp only [Finset.mem_univ])
  intro z _
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro m _
  unfold groupedFactor
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  rintro ⟨j,rfl⟩ _
  rw [atParty_visible]
  rfl

end ThreeFlat.Diagonal.MotifKernel

end OAI
