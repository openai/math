import OAI.Computability.BorderVNP.PackedHistoryAllWordProjection
import OAI.Computability.BorderVNP.PackedHistoryAdapters

/-! # Passing an all-word projection through a full prepared and returned epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP.VerifierNetwork

variable {k b : ℕ} {V W G : ℕ → Type} [∀ j,Fintype (V j)] [∀ j,Fintype (W j)] [∀ j,Fintype (G j)]
variable {pick : ∀ j, V j → W j} {aug : Steps k b W G} {plain : Steps k b V G}
variable {X Y Z U : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype U]

/-- The physical input preparation and final placement may use all child arrays.
When their geometric fields commute on arbitrary valuations and the true inner
kernels do as well, the whole epoch projects on every word and every flag. -/
theorem StepsProject.wrappedEpoch (project : StepsProject pick aug plain) (before : Y → X) (after : U → Z)
    (a : Frame X (Fin (k^b) × W 0)) (v : Frame Y (Fin (k^b) × V 0))
    (endA : Frame (X ⊕ W b) Z) (endV : Frame (Y ⊕ V b) U)
    (prep : ∀ x i j, a.eval x (i,pick 0 j) = v.eval (x ∘ before) (i,j))
    (post : ∀ x y j,endA.eval (Sum.elim x y) (after j) = endV.eval (Sum.elim (x ∘ before) (y ∘ pick b)) j)
    (xg : X ⊕ Slot k G b → Bool) (result : Result U) :
    (PackedHistoryCircuit.wrappedEpoch a aug endA).eval xg (Sum.map after id result) =
      (PackedHistoryCircuit.wrappedEpoch v plain endV).eval (xg ∘ Sum.map before id) result := by
  let x := xg ∘ Sum.inl
  let g := xg ∘ Sum.inr
  have left : xg = Sum.elim x g := by funext z; cases z <;> rfl
  have right : xg ∘ Sum.map before id = Sum.elim (x ∘ before) g := by funext z; cases z <;> rfl
  have mid : Sum.elim (a.eval x) g ∘ Sum.map (Prod.map id (pick 0)) id = Sum.elim (v.eval (x ∘ before)) g := by
    funext z; cases z with
    | inl z => exact prep x z.1 z.2
    | inr z => rfl
  have inside (r : Result (V b)) := (project.flatEpoch (Sum.elim (a.eval x) g) r).trans
    (congrArg (fun y => (PackedHistoryCircuit.flatEpoch plain).eval y r) mid)
  rw [right,left]
  cases result with
  | inr z =>
    cases z
    exact (wrappedEpoch_flag a aug endA x g).trans ((inside (.inr ())).trans (wrappedEpoch_flag v plain endV _ g).symm)
  | inl z =>
    let wa := fun j => (PackedHistoryCircuit.flatEpoch aug).eval (Sum.elim (a.eval x) g) (.inl j)
    let wv := fun j => (PackedHistoryCircuit.flatEpoch plain).eval (Sum.elim (v.eval (x ∘ before)) g) (.inl j)
    have root : wa ∘ pick b = wv := funext fun j => inside (.inl j)
    have terminal := post x wa z
    rw [root] at terminal
    exact (congrFun (wrappedEpoch_state a aug endA x g) (after z)).trans
      (terminal.trans (congrFun (wrappedEpoch_state v plain endV _ g) z).symm)

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
