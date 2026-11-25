import OAI.Hierarchy.CatalystIndependentCopies
import OAI.Hierarchy.CatalystSubstitutionPointwise
import OAI.Hierarchy.TaggedApproximation
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # The tagged-oracle descent interface in terms of actual open networks

The host includes the socket bits of every call in its physical size. Its
exact contraction represents all data and catalyst legs of the independent
copies. The normalization charge comes from `CorrectionBatch.physical_output`.
-/

noncomputable section
namespace Hierarchy.CollapseOracle

open Catalyst CatalystSubstitution CorrectionBatch
open scoped Classical BigOperators
open Filter

variable {F : Type*} [Field F] {k p : ℕ}

def tagCall (h : ℕ) (Y : Approximation F k (Tagged.pins h h)) : Occurrence F k :=
  ⟨Tagged.pins h h, Tagged.coeff F h h, Y⟩

/-- The ordered data sockets of repeated calls depend only on their common arity. -/
def tagSockets (h : ℕ) (Y Z : Approximation F k (Tagged.pins h h)) :
    (t : ℕ) → Sockets (List.replicate t (tagCall h Y)) ≃ Sockets (List.replicate t (tagCall h Z))
  | 0 => Equiv.refl Empty
  | t+1 => Equiv.sumCongr (Equiv.refl _) (tagSockets h Y Z t)

private theorem tagWeight (h : ℕ) (Y Z : Approximation F k (Tagged.pins h h)) (t : ℕ)
    (x : Sockets (List.replicate t (tagCall h Z)) → Bool) :
    exactWeight (List.replicate t (tagCall h Y)) (x ∘ tagSockets h Y Z t) =
      exactWeight (List.replicate t (tagCall h Z)) x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change Tagged.coeff F h h (x ∘ Sum.inl) *
      exactWeight _ ((x ∘ Sum.inr) ∘ tagSockets h Y Z t) =
      Tagged.coeff F h h (x ∘ Sum.inl) * exactWeight _ (x ∘ Sum.inr)
    rw [ih]

private def relabelHost {U V : Type} [Fintype U] [Fintype V] (e : U ≃ V)
    (H : Host F k p U) : Host F k p V where
  width := H.width
  network := H.network.restrictPins (fun i => some (Fintype.equivFin _
    ((Equiv.sumCongr (Equiv.refl (Port p H.width)) e)
      ((Fintype.equivFin (Port p H.width ⊕ U)).symm i))))

private theorem relabel_coeff {U V : Type} [Fintype U] [Fintype V] (e : U ≃ V)
    (H : Host F k p U) (x : Port p H.width → Bool) (s : V → Bool) :
    (relabelHost e H).coeff x s = H.coeff x (s ∘ e) := by
  have split : Sum.elim x s ∘ Equiv.sumCongr (Equiv.refl (Port p H.width)) e =
      Sum.elim x (s ∘ e) := by funext u; cases u <;> rfl
  unfold Host.coeff ThreeFlat.Routing.TypedWiring.value relabelHost
  rw [ThreeFlat.BitNetwork.restrictPins_eval]
  apply congrArg H.network.eval
  funext i
  simp only [Option.map_some,Option.getD_some,Equiv.symm_apply_apply]
  exact congrFun split ((Fintype.equivFin _).symm i)

/-- Keep every physical row and hidden bit in the compiled host while changing
the chosen network implementing each tagged call. -/
def retag (h t : ℕ) (Y Z : Approximation F k (Tagged.pins h h))
    (H : Host F k p (Sockets (List.replicate t (tagCall h Y)))) :
    Host F k p (Sockets (List.replicate t (tagCall h Z))) := relabelHost (tagSockets h Y Z t) H

theorem retag_exact (h t : ℕ) (Y Z : Approximation F k (Tagged.pins h h))
    (H : Host F k p (Sockets (List.replicate t (tagCall h Y)))) (x : Port p H.width → Bool) :
    exactValue (List.replicate t (tagCall h Z)) (retag h t Y Z H) x =
      exactValue (List.replicate t (tagCall h Y)) H x := by
  let e := tagSockets h Y Z t
  unfold exactValue
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
  intro s
  change (relabelHost e H).coeff x s * exactWeight _ s =
    H.coeff x (s ∘ e) * exactWeight _ (s ∘ e)
  rw [relabel_coeff]
  exact congrArg (H.coeff x (s ∘ e) * ·) (tagWeight h Y Z t s).symm

theorem retag_size (h t : ℕ) (Y Z : Approximation F k (Tagged.pins h h))
    (H : Host F k p (Sockets (List.replicate t (tagCall h Y)))) :
    hostSize (retag h t Y Z H) = hostSize H := by
  let e := tagSockets h Y Z t
  change H.network.cells + H.network.internal +
      Fintype.card (Port p H.width ⊕ Sockets (List.replicate t (tagCall h Z))) =
    H.network.cells + H.network.internal +
      Fintype.card (Port p H.width ⊕ Sockets (List.replicate t (tagCall h Y)))
  exact congrArg (H.network.cells+H.network.internal+ ·)
    (Fintype.card_congr (Equiv.sumCongr (Equiv.refl (Port p H.width)) e.symm))

/-- A single compiled host for a canonical replacement has the agreement and
size needed for every subsequent choice of physical tagged implementation. -/
theorem retag_host (h t : ℕ) (Y Z : Approximation F k (Tagged.pins h h))
    (A : Approximation F k p) (H : Host F k p (Sockets (List.replicate t (tagCall h Y))))
    (same : Agrees A (tableApprox H.width (exactValue (List.replicate t (tagCall h Y)) H))) :
    Agrees A (tableApprox (retag h t Y Z H).width
      (exactValue (List.replicate t (tagCall h Z)) (retag h t Y Z H))) ∧
      hostSize (retag h t Y Z H) = hostSize H := by
  obtain ⟨w,coeff⟩ := same
  refine ⟨⟨w,fun x => (coeff x).trans ?_⟩,retag_size h t Y Z H⟩
  exact (tableApprox_coeff H.width (exactValue _ H) x).trans
    ((retag_exact h t Y Z H x).symm.trans
      (tableApprox_coeff H.width (exactValue _ (retag h t Y Z H)) x).symm)

/-- Proposition 'Descent with tagged-permutation gates'. The socket type
uses the replacement's arity alone. The count and replication are uniform
over every implementation of that arity. -/
def OpenNetworks (F : Type*) [Field F] (a C : ℝ) : Prop :=
  ∀ᶠ h : ℕ in atTop,
    ∀ M : ℕ, 2^h≤M → M≤(2^h)^2 → ∀ {k p : ℕ} (X : Approximation F k p),
    10*(X.size+1)≤M → ∃ d t : ℕ, 0<d ∧
      Real.logb 2 d ≤ C*(Real.logb 2 (2*(h:ℝ)))^2 ∧
      ∀ Y : Approximation F k (Tagged.pins h h),
      let os := List.replicate t (tagCall h Y)
      ∃ H : Host F k (d*p) (Sockets os),
        Agrees (independentCopies d X) (tableApprox H.width (exactValue os H)) ∧
          (hostSize H : ℝ) ≤ C*d*((M:ℝ)/(h:ℝ)^a + Fintype.card (Port p X.width))

def Descent (F : Type*) [Field F] : Prop :=
  ∃ a C : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ OpenNetworks F a C

omit [Field F] in
private theorem socket_count (o : Occurrence F k) (t : ℕ) :
    Fintype.card (Sockets (List.replicate t o)) = t*o.arity := by
  induction t with
  | zero => simp [Sockets]
  | succ t ih => simp [List.replicate_succ,Sockets,ih,Nat.succ_mul,Nat.add_comm]

omit [Field F] in
/-- Every tagged bit incidence in this ordered bank is present in the host. -/
theorem incidences (o : Occurrence F k) (t : ℕ) (H : Host F k p (Sockets (List.replicate t o))) :
    t*o.arity ≤ hostSize H := by
  simp only [hostSize,Fintype.card_sum,socket_count]
  omega

omit [Field F] in
private theorem replicate_min (o : Occurrence F k) (t : ℕ) (u v : ℝ) :
    min u v ≤ commonGap u (fun _ => v) (List.replicate t o) := by
  induction t with
  | zero => exact min_le_left _ _
  | succ t ih => simpa [List.replicate_succ,commonGap] using le_min (min_le_right u v) ih

/-- Install the same exposed cheap tag at every actual native call. Original
public data may be pinned differently in every replicated tick. -/
theorem install_tags (h d t : ℕ) (Y : Approximation F k (Tagged.pins h h))
    (X : Approximation F k p) (f : (Fin p → Bool) → F) {D S : ℝ}
    (hk : 0<k) (nonneg : 0≤D) (old : X.PointwiseGap f D)
    (tag : Y.Gap (Tagged.coeff F h h) S)
    (H : Host F k (d*p) (Sockets (List.replicate t (tagCall h Y))))
    (good : Agrees (independentCopies d X)
      (tableApprox H.width (exactValue (List.replicate t (tagCall h Y)) H))) :
    let os := List.replicate t (tagCall h Y)
    let Z := install os H
    Z.PointwiseGap (CorrectionFrame.dataProduct d f) (min (D-2*k*d) S - 2*k*t) ∧
      Z.size + t*Tagged.pins h h = hostSize H + t*Y.size := by
  let o := tagCall h Y
  let os := List.replicate t o
  have powered := independentCopies_gap d X f hk nonneg old
  have calls : ∀ z ∈ os, z.replacement.Gap z.target S := by
    intro z hz
    rcases List.eq_of_mem_replicate hz with rfl
    exact tag
  have installed := install_pointwise os H _ good _ _ (fun _ => S) powered calls
  constructor
  · intro P pin
    apply (installed P pin).imp_right
    intro price
    have hmin := replicate_min o t (D-2*k*d) S
    simp only [os,List.length_replicate] at price
    exact price.trans (sub_le_sub_left (sub_le_sub_right hmin (2*k*t)) _)
  · simpa [os,o,tagCall,List.map_replicate,List.sum_replicate,Nat.mul_comm] using install_size os H


end Hierarchy.CollapseOracle

end
end OAI
