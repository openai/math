import OAI.Hierarchy.DescentObservedHardware

namespace OAI
/-! # Compile a real powered rotor after reassigning all output-socket row names -/

namespace Hierarchy.DescentChosenRouter
open DescentColonies DescentRotor DescentBaseProfile DescentRouterSlots
open scoped Classical BigOperators
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
variable {k n : ℕ} (P : Placement V I H A k (2^n))
local notation "Y" => (2^n:ℕ)

def relabel (σ : Bool→P.Good→Equiv.Perm (Fin Y)) : Placement V I H A k Y :=
  {P with columns:=fun s g=>(P.columns s g).trans (σ s g)}

private theorem permuted_count (σ : Bool→P.Good→Equiv.Perm (Fin Y)) (s : Bool)
    (g : P.Good) (i j : Fin Y) (after : Fintype (Cells (relabel P σ) s g))
    (before : Fintype (Cells P s g)) :
    @matrixOfBundles _ after Y (source (relabel P σ) s g) (target (relabel P σ) s g) i j =
      @matrixOfBundles _ before Y (source P s g) (target P s g) i ((σ s g).symm j) := by
  unfold matrixOfBundles
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  have membership {E : Type} (ft : Fintype E) (q : E → Prop) (dec : DecidablePred q) (x : E) :
      x ∈ @Finset.filter E q dec (@Finset.univ E ft) ↔ q x :=
    (@Finset.mem_filter E q dec (@Finset.univ E ft) x).trans
      ⟨And.right, fun h => ⟨@Finset.mem_univ E ft x, h⟩⟩
  refine (membership after _ _ p).trans (Iff.trans ?_ (membership before _ _ p).symm)
  exact and_congr_right' (σ s g).eq_symm_apply.symm

theorem reRow (σ : Bool→P.Good→Equiv.Perm (Fin Y)) (s : Bool) (g : P.Good) (i j : Fin Y) :
    matrixOfBundles (source (relabel P σ) s g) (target (relabel P σ) s g) i j=
      matrixOfBundles (source P s g) (target P s g) i ((σ s g).symm j) :=
  permuted_count P σ s g i j _ _

variable {F : Type} [Field F] {h C w u : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<w) (hu : 0<u)
variable (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F G.arcs C w p)
variable {B factor : ℝ} (ub : (u:ℝ)≤B) (price : ((2^n:ℕ):ℝ)^2*w≤factor)
include hu menu ub price in
theorem relabel_hardware (σ : Bool→P.Good→Equiv.Perm (Fin Y))
    (rows : ∀s g i,(∑j,(matrixOfBundles (source P s g) (target P s g) i j:ℝ))≤9*factor*B/(Y*u:ℕ))
    (cols : ∀s g j,(∑i,(matrixOfBundles (source P s g) (target P s g) i j:ℝ))≤9*factor*B/(Y*u:ℕ)) :
    Nonempty (Hardware (K:=F) (C₀:=C) (u:=u) (relabel P σ) G hw (factor*B)) := by
  constructor
  apply build (F:=factor) (B:=B) (relabel P σ) G hw hu menu ub price
  · intro s g i
    refine Eq.trans_le ?_ (rows s g i)
    exact Fintype.sum_equiv (σ s g).symm _ _ fun j =>
      congrArg (fun t : ℕ => (t : ℝ)) (permuted_count P σ s g i j _ _)
  · intro s g j
    refine Eq.trans_le ?_ (cols s g ((σ s g).symm j))
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (fun t : ℕ => (t : ℝ)) (permuted_count P σ s g i j _ _)

end
end Hierarchy.DescentChosenRouter

end OAI
