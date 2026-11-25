import OAI.ThreeFlat.Diagonal.PhysicalStage
import OAI.ThreeFlat.Diagonal.RefreshTableStep

namespace OAI
/-! # A full expander refresh as an adaptive transition on the numbered physical graph -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped BigOperators Classical
noncomputable section
variable {m lanes hbits rem h pad : ℕ} {F : Type} [Field F]
variable {c : Fin m → Fin m → ℕ} {C γ : ℝ} (T : RefreshMotif.Table F c (1+h+pad) C)
  (A : State m lanes) (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0 < h) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
  (zero : ∀ i, c i i=0) (conn : Bound (transition c h) ℝ γ)

private def refreshChart (V P L : Type) : (V×P)×L ≃ (V×L)×P where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

abbrev refreshInput := A.width ∘ (StageAddress.refreshEdge u port).symm
abbrev refreshBranches := RefreshMotif.Table.Branch T (changeLanes A.graph u) port (refreshInput A u port)

private def refreshRules : Rewrite A.shape F :=
  (StageAddress.refreshInputIso A.graph A.chart u port A.width).rewrite
    (T.step (changeLanes A.graph u) port (refreshInput A u port) hm hh sym rows zero conn)

private def refreshState (i : Fin (Fintype.card (refreshBranches T A u port))) :
    State (1+h+pad) rem := by
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  let G := changeLanes A.graph u
  let w := refreshInput A u port
  let x : refreshBranches T A u port := (Fintype.equivFin _).symm i
  exact {
    Base := A.Base × Fin m
    order := productOrder A.order (Equiv.refl _)
    Site := (A.Base × BitWord rem) × Fin m
    chart := refreshChart _ _ _
    graph := RefreshTies.outputGraph G c sym rows zero hm pad
    width := RefreshTies.freshWidth c rows (RefreshTies.termWidth c w (T.widths G port w x)) pad }

private theorem card_instances {α : Type} (i j : Fintype α) :
    @Fintype.card α i = @Fintype.card α j := by cases Subsingleton.elim i j; rfl

private theorem choice_instances {α : Type} (i j : Fintype α) (t : Fin (@Fintype.card α i))
    (eqn : @Fintype.card α i = @Fintype.card α j) :
    (@Fintype.equivFin α i).symm t = (@Fintype.equivFin α j).symm (Fin.cast eqn t) := by
  cases Subsingleton.elim i j
  rfl

private theorem refreshRules_count :
    (refreshRules T A u port hm hh sym rows zero conn).count = Fintype.card (refreshBranches T A u port) := by
  dsimp only [refreshRules, HistoryRelabel.Iso.rewrite, RefreshMotif.Table.step, RefreshTies.histogramStep,
    RefreshTies.slotRewrite, RefreshTies.refreshRewrite]
  exact card_instances _ _

set_option maxHeartbeats 400000 in
/-- The refreshed state has one external slot, `h` expander slots and `pad` cyclic padding slots
per physical port. The original lift supplies the actual permuted incidence at the external slot. -/
def refreshMove : Move F A (1+h+pad) rem where
  rules := refreshRules T A u port hm hh sym rows zero conn
  next := fun i => refreshState T A u port hm sym rows zero
    (Fin.cast (refreshRules_count T A u port hm hh sym rows zero conn) i)
  target_eq := fun i => by
    dsimp only [refreshRules, HistoryRelabel.Iso.rewrite, RefreshMotif.Table.step, RefreshTies.histogramStep,
      RefreshTies.slotRewrite, RefreshTies.refreshRewrite, State.shape, StageAddress.shape, refreshState]
    let G := changeLanes A.graph u
    let out := RefreshTies.outputGraph G c sym rows zero hm pad
    let phi (x : refreshBranches T A u port) : Shape :=
      SlotRefinement.shape (RefreshTies.actualPortGraph out)
        (fun e => Fin (2^RefreshTies.freshWidth c rows
          (RefreshTies.termWidth c (refreshInput A u port) (T.widths G port (refreshInput A u port) x)) pad e))
    have graph (Q : LiftedSlots (A.Base × Fin m) (1+h+pad) (BitWord rem)) :
        StageAddress.portGraph Q (refreshChart A.Base (Fin m) (BitWord rem)) =
          RefreshTies.actualPortGraph Q := rfl
    rw [graph]
    exact congrArg phi (@choice_instances (refreshBranches T A u port) _ _ i
      (refreshRules_count T A u port hm hh sym rows zero conn))

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
