import OAI.ThreeFlat.Diagonal.TracePlanForest
import OAI.ThreeFlat.Diagonal.TraceCursorWordLayout

namespace OAI
/-! # Identification of the initial trace forest form with the native word layout -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor LaneCursor.RowLayout TraceSuffix TraceSourceOwner HistoryContraction
open scoped BigOperators Classical
variable {F : Type} [Field F] [Fintype F] {w p r k S base f q low T : ℕ}
variable (M : Machine w p r k) (t : NativeTrace.Fits M S base ((q+1)+low) f)
  (hF : Fintype.card F≤2^w) (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)

def seedExt (T low : ℕ) (v : Fin (q+1)×Lane (q+1)) :=
  if v.1=0 then retained T low (finFunctionFinEquiv v.2).val else 0

def seedPin (_span : 2*T≤S) (low : ℕ) (v : Fin (q+1)×Lane (q+1)) (pin : Fin (2*T)→Bool)
    (j : Fin (seedExt T low v)) : Bool :=
  pin ⟨laneStart low (finFunctionFinEquiv v.2).val+j.val,at_true (by
    by_cases e : v.1=0
    · simpa only [seedExt,e,ite_true] using j.isLt
    · have h := j.isLt; simp [seedExt,e] at h)⟩

/-- Absolute interleaved H endpoint ordinal of a cursor-zero seed pin. The
other cursor sites have empty external pin types. -/
def seedEndpoint (T low : ℕ) (v : Fin (q+1)×Lane (q+1)) (j : Fin (seedExt T low v)) : Fin (2*T) :=
  ⟨laneStart low (finFunctionFinEquiv v.2).val+j.val,at_true (by
    by_cases e : v.1=0
    · simpa only [seedExt,e,ite_true] using j.isLt
    · have h:=j.isLt; simp [seedExt,e] at h)⟩

theorem seedPin_eq_endpoint (span : 2*T≤S) (v : Fin (q+1)×Lane (q+1)) (pin : Fin (2*T)→Bool)
    (j : Fin (seedExt T low v)) : seedPin span low v pin j=pin (seedEndpoint T low v j) := rfl

noncomputable def seedWordLayout (span : 2*T≤S) : WordLayout (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).shape.graph (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).width (Fin (2*T)→Bool) :=
  B.cursorLayout hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells (seedExt T low) (seedPin span low)

variable (span : 2*T≤S) (pub : ℕ→Bool)

private theorem seedWidth (v : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).Site) : (seedForm M t hF st B hk span pub).width v=(seedWordLayout M t hF st B hk span).ports.form.width v := by
  rcases v with ⟨i,L⟩
  apply (seedForm_width M t hF st B hk span pub i L).trans
  exact congrArg (fun n => seedExt T low (i,L) + n)
    (B.cursor_half_width hk low (1+(((q+1)+low)+((q+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells
      (seedExt T low) (seedPin span low) (i,L))

/-- Every program pin agrees as an absolute bit ordinal, including both bank
boundaries when the clipped set of external endpoints is empty. -/
theorem seedForm_eq_word : (seedForm M t hF st B hk span pub)=(seedWordLayout M t hF st B hk span).ports.form := by
  apply Form.ext_read (seedForm M t hF st B hk span pub) (seedWordLayout M t hF st B hk span).ports.form (seedWidth M t hF st B hk span pub)
  rintro ⟨i,L⟩ pin x j
  let I := bitIndex hF t.width t.labels base st t.header t.time r k t.grid L
  let out := B.cursorOut hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells i L x
  let inc := B.cursorIn hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells i L x
  have width := B.cursor_half_width hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells (seedExt T low) (seedPin span low) (i,L)
  have wires := B.cursor_encode hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells (seedExt T low) (seedPin span low) (i,L) x
  have atport (a : Fin (BucketIndex.ports B.cursorCopies I.t)) :
      RelayNetwork.pins I.tag out inc a=(seedWordLayout M t hF st B hk span).ports.encode (i,L) x (Fin.cast width a) := (congrFun wires a).symm
  let agrees (leaf : SiteLeaf F (Fin (2*T)→Bool) _) : Prop :=
    ∀ (same : leaf.width = (seedWordLayout M t hF st B hk span).ports.form.width (i,L))
      (a : Fin leaf.width), leaf.read pin out inc a =
        (seedWordLayout M t hF st B hk span).ports.form.read (i,L) pin x (Fin.cast same a)
  suffices matched : agrees (cursorAtom M t hF st B.cursorCopies T span pub i L) from
    matched (seedWidth M t hF st B hk span pub (i,L)) j
  by_cases first : i=0
  · simp only [cursorAtom,ite_eq_left first]
    intro same a
    have e : retained T low (finFunctionFinEquiv L).val=seedExt T low (i,L) := by
      simp [seedExt,first]
    exact append_cast_read e width (localPairPins span pin low (finFunctionFinEquiv L).val)
      (RelayNetwork.pins I.tag out inc) (seedPin span low (i,L) pin)
      ((seedWordLayout M t hF st B hk span).ports.encode (i,L) x) (fun _ => rfl) atport a
  · simp only [cursorAtom,ite_eq_right first]
    intro same a
    have e : seedExt T low (i,L)=0 := by simp [seedExt,first]
    have pos : Fin.cast same a =
        Fin.natAdd (seedExt T low (i,L)) (Fin.cast width a) := by
      apply Fin.ext
      change a.val = seedExt T low (i,L) + a.val
      rw [e, Nat.zero_add]
    change RelayNetwork.pins I.tag out inc a =
      Fin.append (seedPin span low (i,L) pin) ((seedWordLayout M t hF st B hk span).ports.encode (i,L) x)
        (Fin.cast same a)
    let left := seedPin span low (i,L) pin
    let right := (seedWordLayout M t hF st B hk span).ports.encode (i,L) x
    exact (atport a).trans ((Fin.append_right left right (Fin.cast width a)).symm.trans
      (congrArg (Fin.append left right) pos.symm))

/-- The stage constructor can use its native word layout without a separate
hypothesis identifying the compiled root form. -/
noncomputable def seedWordForest : Forest F (seedWordLayout M t hF st B hk span).ports.form :=
  seedForm_eq_word M t hF st B hk span pub ▸ seedForest M t hF st B hk span pub

omit [Fintype F] in
private theorem transported_values {Z : HistoryContraction.Shape} {X : Type} {C E : Form Z X} (h : C=E)
    (N : Forest F C) (x : X) : E.values (h ▸ N) x=C.values N x := by
  subst E
  rfl

theorem seedWordForest_values (pin : Fin (2*T)→Bool) :
    (seedWordLayout M t hF st B hk span).ports.form.values (seedWordForest M t hF st B hk span pub) pin =
      (seedForm M t hF st B hk span pub).values (seedForest M t hF st B hk span pub) pin :=
  transported_values (seedForm_eq_word M t hF st B hk span pub) _ pin

/-- The actual stage-by-stage word-layout assembly consumes precisely these
leaves and produces the native matrix entry after the final contraction. -/
theorem contract_prepared_word_plan (R : PhysicalStage.Run F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells)) (I : RAM.PhysicalPrelude.Image F w)
    (D : Fin I.advice→Bool) (params : Fin I.parameters→Bool) (extent : 2*I.endpointBits≤S)
    (sep : 2*I.endpointBits≤base)
    (assembly : R.plan.Assembly (seedWordLayout M t hF st B hk extent).ports.form)
    (x y : Fin I.endpointBits→Bool) :
    let N := seedWordForest M t hF st B hk extent (publicAt I base (NativeTrace.executable M) D params)
    (∑ h : R.plan.History, ∑ b : (R.plan.finish h).Boundary, ∏ v,
      (R.plan.assemble h assembly N).1.values (R.plan.assemble h assembly N).2 (endpointPin x y) v
        ((R.plan.finish h).graph.atVertex b v)) =
      (NativeTrace.network M t hF st).eval (advicePins base (NativeTrace.executable M) (I.tapeBit D x y params)) := by
  let pub := publicAt I base (NativeTrace.executable M) D params
  let U := B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells
  let form := (seedWordLayout M t hF st B hk extent).ports.form
  let forest := seedWordForest M t hF st B hk extent pub
  let pin := endpointPin x y
  exact (R.plan.contract_eq_networks form assembly forest pin).symm.trans
    ((congrArg U.shape.contract (seedWordForest_values M t hF st B hk extent pub pin)).trans
      ((contract_seedForest M t hF st B hk extent pub pin).trans
        (native_cursor_trace M t hF st hk I D params extent sep x y)))


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
