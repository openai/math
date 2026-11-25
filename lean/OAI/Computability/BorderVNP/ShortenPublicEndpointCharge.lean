import OAI.Computability.BorderVNP.ShortenPublicEndpointSuccessor
import OAI.Computability.BorderVNP.ShortenCombiningConcentration

/-!
# Successor charge flags on the physical sewn network

Hooks and bank cables are charged. Each retained interval inherits its old
cable's charge, so a present frozen cable can keep its width and both sites
while being excluded from the next shortening population.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints.Successor

open Crossing StaticRows SeedIntervals CombiningStep VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A : Type} [Fintype A] (B : Type*) [Fintype B]
variable (nSites nEdges w : ℕ) {nSeeds : ℕ} (seed : A ≃ Fin nSeeds)

private abbrev Pins := Source e B A nSites nEdges nSeeds w ⊕
  Next B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w

/-- Append one successor charge bit to every row while retaining its separate occupancy. -/
abbrev Charged (B : Type*) (sites edges w : ℕ) := Next B sites edges w ⊕ Fin edges

private def inherited : Serializer.Row nEdges D ⊕ (A × TemplateEdge e) → Expr (Pins (A := A) (nSeeds := nSeeds) e B nSites nEdges w)
  | .inr _ => .const true
  | .inl r => if r.2.2.val = 2 then .input (.inl (.inr (.inl (r,.inl .charged)))) else .const true

private noncomputable def chargeBit (i : Fin (edgeCapacity e nEdges nSeeds)) : Expr (Pins (A := A) (nSeeds := nSeeds) e B nSites nEdges w) :=
  (.input (.inr (.inr i)) : Expr (Pins (A := A) (nSeeds := nSeeds) e B nSites nEdges w)).and
    (inherited e B nSites nEdges w ((candidateEquiv e nEdges seed).symm i))

variable (f : Frame (Source e B A nSites nEdges nSeeds w) (Next B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w))

/-- Charge computation using shared presence bits from the completed successor serializer. -/
noncomputable def withCharges : Frame (Source e B A nSites nEdges nSeeds w)
    (Charged B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w) :=
  let reads := (Frame.initial id).step (chargeBit e B nSites nEdges w seed)
  (reads.withInput.select (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)).subst f.withInput

omit [NeZero D] in
/-- Each reserved cable row incurs at most three gates for the successor charge. -/
theorem withCharges_size : (withCharges e B nSites nEdges w seed f).size ≤ f.size + 3 * edgeCapacity e nEdges nSeeds := by
  have single (i : Fin (edgeCapacity e nEdges nSeeds)) : (chargeBit e B nSites nEdges w seed i).size ≤ 3 := by
    unfold chargeBit inherited
    cases (candidateEquiv e nEdges seed).symm i with
    | inr _ => exact le_rfl
    | inl r => by_cases hr : r.2.2.val = 2 <;> simp [hr,StatementCircuit.Expr.size]
  have hs := Frame.step_size_le (Frame.initial id) _ 3 single
  simp only [Frame.initial_size,Fintype.card_fin,zero_add] at hs
  simpa only [withCharges,Frame.subst_size,Frame.select_size,Frame.withInput_size,Nat.mul_comm 3] using Nat.add_le_add_left hs f.size

variable (x : Source e B A nSites nEdges nSeeds w → Bool)

omit [NeZero D] in
/-- Site and cable bits, including occupancy, agree with the previous frame. -/
theorem withCharges_table (j : Next B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) w) :
    (withCharges e B nSites nEdges w seed f).eval x (.inl j) = f.eval x j := by
  simp [withCharges]

omit [NeZero D] in
private theorem withCharges_read (i : Fin (edgeCapacity e nEdges nSeeds)) :
    (withCharges e B nSites nEdges w seed f).eval x (.inr i) = (f.eval x (.inr i) &&
      (((candidateEquiv e nEdges seed).symm i).elim
        (fun r => if r.2.2.val = 2 then x (.inr (.inl (r,.inl .charged))) else true)
        (fun _ => true))) := by
  simp only [withCharges,Frame.subst_eval,Frame.select_eval,Sum.elim_inr,Frame.withInput_eval_inr,
    Frame.step_eval,chargeBit,StatementCircuit.Expr.eval,Frame.initial_eval,id_eq]
  cases (candidateEquiv e nEdges seed).symm i with
  | inr _ => rfl
  | inl r => by_cases h : r.2.2.val = 2 <;> simp [inherited,h,StatementCircuit.Expr.eval]

variable {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
variable (oldSite : p.layout.Site ↪ Fin nSites) (old : p.layout.Edge ↪ Fin nEdges)
variable (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A) (first : Fin D × Bool) (q : Counts e p bin perm)
variable (src : SourceData e p bin perm positive oldSite old seed dummy first q x)
variable (out : Result e p bin perm positive oldSite old seed dummy first q x (f.eval x))

include src out in
/-- Every physical cable's stored charge is the exact geometric post-mask of the sewn pack. -/
theorem withCharges_edge (z : EdgeShape e p bin perm) :
    (withCharges e B nSites nEdges w seed f).eval x (.inr (edgeRows e p bin perm old seed.toEmbedding z)) =
      postMask p bin perm e positive q z := by
  have present : f.eval x (.inr (edgeRows e p bin perm old seed.toEmbedding z)) = true := (out.occupied _).mpr ⟨z,rfl⟩
  rw [withCharges_read,present,Bool.true_and]
  rcases z with (u | u) | c | ⟨a,v⟩
  · let r : Serializer.Row nEdges D := (old u.val.1,u.val.2,0)
    have hz : edgeRows e p bin perm old seed.toEmbedding (.inl (.inl u)) = candidateEquiv e nEdges seed (.inl r) :=
      (hook_candidate e p bin perm old seed.toEmbedding u).1.trans (candidateEquiv_old e nEdges seed r).symm
    rw [hz,Equiv.symm_apply_apply]
    rfl
  · let r : Serializer.Row nEdges D := (old u.val.1,u.val.2,1)
    have hz : edgeRows e p bin perm old seed.toEmbedding (.inl (.inr u)) = candidateEquiv e nEdges seed (.inl r) :=
      (hook_candidate e p bin perm old seed.toEmbedding u).2.trans (candidateEquiv_old e nEdges seed r).symm
    rw [hz,Equiv.symm_apply_apply]
    rfl
  · let r : Serializer.Row nEdges D := (old c.val.1,c.val.2,2)
    have hz : edgeRows e p bin perm old seed.toEmbedding (.inr (.inl c)) = candidateEquiv e nEdges seed (.inl r) :=
      (retained_candidate e p bin perm old seed.toEmbedding c).trans (candidateEquiv_old e nEdges seed r).symm
    rw [hz,Equiv.symm_apply_apply]
    exact ((src.directory r).flags c.val.1 rfl).1
  · rw [← candidateEquiv_bank e p bin perm old seed a v,Equiv.symm_apply_apply]
    rfl

include out in
/-- Every reserved hole is inactive, independently of its stale inherited charge word. -/
theorem withCharges_hole (i : Fin (edgeCapacity e nEdges nSeeds)) (hi : i ∉ Set.range (edgeRows e p bin perm old seed.toEmbedding)) :
    (withCharges e B nSites nEdges w seed f).eval x (.inr i) = false := by
  have hn : f.eval x (.inr i) = false := Bool.not_eq_true _ |>.mp ((out.occupied i).not.mpr hi)
  rw [withCharges_read,hn,Bool.false_and]

end Shortening.PublicEndpoints.Successor

end BorderVNP
end Computability
end OAI
