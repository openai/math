import OAI.Hierarchy.DescentSeedNativeCells
import OAI.Hierarchy.DescentPackedSeedCensus
import OAI.Hierarchy.DescentPackedActorRaster

namespace OAI
/-! # A physical occupancy pin for every initial vertex at every old block -/

namespace Hierarchy.DescentInitialHost.PackedSeed
open Catalyst DescentSIMDLookup DescentColonies DescentActorRaster
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option Elab.async false

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
variable {R s : ℕ} (c : (initialGroup X R s).Choice)
local notation "W" => (initialGroup X R s).state c
local notation "N" => X.network.copyGraph
variable {J : Type} [Fintype J] [DecidableEq J] {l : ℕ} (digits : Fin R ≃ J×DescentColonies.Block l)

omit [Fintype J] [DecidableEq J] in
theorem actor_present (v : Site N) (g : J) (x : DescentColonies.Block l) :
    ∃u : (W).graph.Site,seedPos X c digits u=(g,v) ∧ seedBlock X c digits u=x := by
  refine ⟨⟨digits.symm (g,x),v⟩,?_,?_⟩ <;> simp [seedPos,seedBlock]

variable {H L M w : ℕ} (host : Site X.network.copyGraph ↪ Fin H)
def actorMem (X : Approximation F k p) (host : Site X.network.copyGraph ↪ Fin H)
    (l M L base : ℕ) (m : Memory w) : Memory w :=
  mount base (fun j : Fin (H*chunks L M)=>
    (((data (fun v (_ : Fin L)=>actorRow X host l v) ((row H L M).symm j)).val:ℕ):Word w)) m

theorem actor_header_read (base : ℕ) (m : Memory w) (p : Row H L M) :
    actorMem X host l M L base m (base+(row H L M p).val) =
      ((data (fun v (_ : Fin L)=>actorRow X host l v) p).val:Word w) := by
  simp [actorMem,mounted]

omit [Fintype J] in
theorem actor_real (v : Site N) (g : J) :
    actorRow X host l (host v)=DescentActorRaster.actorMask (seedPos X c digits) (seedBlock X c digits) (g,v) := by
  unfold actorRow DescentActorRaster.actorMask
  apply congrArg (encode 1 _)
  funext x
  have here : ∃ u, host u = host v := ⟨v, rfl⟩
  exact (ite_eq_left here).trans (ite_eq_left (actor_present X c digits v g x)).symm

/-- Every bit of the actor mask is clear for a padded host. -/
theorem actor_padded (v : Fin H) (empty : ¬ ∃ u, host u = v) :
    actorRow X host l v = 0 := by
  simp only [actorRow, ite_eq_right empty]
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin (2 ^ l) => (0 : Cell 1))).val = 0
  simp []

end
end Hierarchy.DescentInitialHost.PackedSeed

end OAI
