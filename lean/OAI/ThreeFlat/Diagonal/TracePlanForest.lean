import OAI.ThreeFlat.Diagonal.TraceCursorAtoms
import OAI.ThreeFlat.Diagonal.TraceCursorBoundary

namespace OAI
/-! # Contraction of the physically addressed initial history forest -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor LaneCursor.RowLayout TraceSuffix RAM.PhysicalPrelude
open HistoryContraction
open scoped BigOperators Classical
variable {F : Type} [Field F] [Fintype F] {w p r k S base f q low T : ℕ}
variable (M : Machine w p r k) (t : NativeTrace.Fits M S base ((q+1)+low) f)
  (hF : Fintype.card F≤2^w) (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
variable (span : 2*T≤S) (pub : ℕ→Bool)

noncomputable def seedForm : Form (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).shape (Fin (2*T)→Bool) where
  width v := (cursorAtom M t hF st B.cursorCopies T span pub v.1 v.2).width
  read v pin x := (cursorAtom M t hF st B.cursorCopies T span pub v.1 v.2).read pin
    (B.cursorOut hk low (1+(((q+1)+low)+((q+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells v.1 v.2 x) (B.cursorIn hk low (1+(((q+1)+low)+((q+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells v.1 v.2 x)

noncomputable def seedForest : Forest F (seedForm M t hF st B hk span pub) :=
  fun v => .atom (cursorAtom M t hF st B.cursorCopies T span pub v.1 v.2).table

theorem seedForm_width (i : Fin (q+1)) (L : Lane (q+1)) :
    (seedForm M t hF st B hk span pub).width (i,L) =
      (if i=0 then retained T low (finFunctionFinEquiv L).val else 0)+
      BucketIndex.ports B.cursorCopies (TraceSourceOwner.bitIndex hF t.width t.labels base st t.header t.time r k t.grid L).t :=
  cursorAtom_width M t hF st B.cursorCopies T span pub i L

/-- Port states have the same word/bit numbering as the first-layer emitter. -/
theorem seedForm_values (pin : Fin (2*T)→Bool) :
    (seedForm M t hF st B hk span pub).values (seedForest M t hF st B hk span pub) pin =
      B.cursorFactor hk low (1+(((q+1)+low)+((q+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells (fun i L send recv =>
        (cursorAtom M t hF st B.cursorCopies T span pub i L).table.eval ((cursorAtom M t hF st B.cursorCopies T span pub i L).read pin send recv)) := rfl

theorem contract_seedForest (pin : Fin (2*T)→Bool) :
    (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).shape.contract ((seedForm M t hF st B hk span pub).values (seedForest M t hF st B hk span pub) pin) =
      ∑ z : Fields (q+1) B.cursorCopies (Fin (1+(((q+1)+low)+((q+1)+low)))) (PayloadAddress low (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells),
        ∏ i, ∏ L, nativeCursorFactor M t hF st span pub pin hk z i L := by
  rw [seedForm_values,B.cursor_contract]
  simp_rw [cursorAtom_eval]

/-- Summing the actual compiled terminal forests at their true terminal edge
assignments recovers the original native H matrix entry. -/
theorem contract_prepared_plan (R : PhysicalStage.Run F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells)) (I : Image F w) (D : Fin I.advice→Bool)
    (params : Fin I.parameters→Bool) (extent : 2*I.endpointBits≤S) (sep : 2*I.endpointBits≤base)
    (U : R.plan.Assembly (seedForm M t hF st B hk extent (publicAt I base (NativeTrace.executable M) D params)))
    (x y : Fin I.endpointBits→Bool) :
    let N := seedForest M t hF st B hk extent (publicAt I base (NativeTrace.executable M) D params)
    (∑ h : R.plan.History, ∑ b : (R.plan.finish h).Boundary, ∏ v,
      (R.plan.assemble h U N).1.values (R.plan.assemble h U N).2 (endpointPin x y) v
        ((R.plan.finish h).graph.atVertex b v)) =
      (NativeTrace.network M t hF st).eval (advicePins base (NativeTrace.executable M) (I.tapeBit D x y params)) := by
  dsimp only
  rw [←R.plan.contract_eq_networks,contract_seedForest]
  exact native_cursor_trace M t hF st hk I D params extent sep x y


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
