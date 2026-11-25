import OAI.ThreeFlat.Diagonal.PhysicalLocalTariff
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace
import OAI.ThreeFlat.Diagonal.TraceSeedWordForm
import OAI.ThreeFlat.Diagonal.HistoryInitialCharge
import OAI.ThreeFlat.Diagonal.TraceEndpointInterval
import OAI.ThreeFlat.Diagonal.TraceSeedWork

namespace OAI
/-! # Charges of the original physically emitted trace leaves -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor LaneCursor.RowLayout TraceSuffix TraceSourceOwner HistoryContraction
open scoped BigOperators Classical
variable {F : Type} [Field F] [Fintype F] {w p r k S base f q low T : ℕ}
variable (M : Machine w p r k) (t : NativeTrace.Fits M S base ((q+1)+low) f)
  (hF : Fintype.card F≤2^w) (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
variable (span : 2*T≤S) (pub : ℕ→Bool)

private def leafCharge {Pins Half : Type} (leaf : SiteLeaf F Pins Half) :=
  leaf.table.internal + leaf.table.cells + 1

private theorem relay_charge (i : Fin (q+1)) (L : Lane (q+1)) (other : i ≠ 0) :
    let I := bitIndex hF t.width t.labels base st t.header t.time r k t.grid L
    ((seedForest M t hF st B hk span pub) (i,L)).resources =
      1+(B.cursorCopies+1)*2*I.t+I.t := by
  let I := bitIndex hF t.width t.labels base st t.header t.time r k t.grid L
  change leafCharge (cursorAtom M t hF st B.cursorCopies T span pub i L) = _
  unfold cursorAtom
  dsimp only
  rw [ite_eq_right other]
  exact I.relay_resources (r:=B.cursorCopies) i

set_option maxHeartbeats 1500000 in
theorem leaf_resources (i : Fin (q+1)) (L : Lane (q+1)) :
    ((seedForest M t hF st B hk span pub) (i,L)).resources ≤ 1+2^low*(2*(TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride+(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells+12*(B.cursorCopies+1)*(1+(((q+1)+low)+((q+1)+low)))*(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) := by
  let I := bitIndex hF t.width t.labels base st t.header t.time r k t.grid L
  let addr := bitAddress hF t.width t.labels base st t.header t.time r k t.grid L I
  have major := I.rectangular_charge (r:=B.cursorCopies) addr i rfl rfl
  by_cases first : i=0
  · subst i
    change leafCharge (cursorAtom M t hF st B.cursorCopies T span pub 0 L) ≤ _
    unfold cursorAtom
    dsimp only
    rw [ite_eq_left rfl]
    simp only [leafCharge,pairLeaf,TraceSuffix.network]
    simpa only [Tree.resources_atom] using major
  · rw [relay_charge M t hF st B hk span pub i L first]
    rw [I.first_resources] at major
    change 1+(B.cursorCopies+1)*2*I.t+I.t ≤ _
    exact le_trans (by omega) major

theorem forest_resources :
    (∑ v : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).Site, ((seedForest M t hF st B hk span pub) v).resources) ≤ ((q+1)*2^(q+1))*(1+2^low*(2*(TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride+(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells+12*(B.cursorCopies+1)*(1+(((q+1)+low)+((q+1)+low)))*(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells)) := by
  calc
    _ ≤ ∑ _ : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).Site, (1+2^low*(2*(TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride+(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells+12*(B.cursorCopies+1)*(1+(((q+1)+low)+((q+1)+low)))*(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells)) := Finset.sum_le_sum fun v _ => leaf_resources M t hF st B hk span pub v.1 v.2
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact congrArg (· * (1+2^low*(2*(TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride+(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells+12*(B.cursorCopies+1)*(1+(((q+1)+low)+((q+1)+low)))*(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells))) (B.cursorState_positions hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells)

omit [Field F] [Fintype F] in
private theorem cast_resource {Z : HistoryContraction.Shape} {X : Type} {V W : Form Z X} (e : V=W)
    (leaf : Forest F V) (v : Z.Site) : ((e ▸ leaf : Forest F W) v).resources=(leaf v).resources := by
  subst W
  rfl

theorem seedWordForest_resources (v : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).Site) :
    ((seedWordForest M t hF st B hk span pub) v).resources≤1+2^low*(2*(TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride+(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells+12*(B.cursorCopies+1)*(1+(((q+1)+low)+((q+1)+low)))*(TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) :=
  (cast_resource (seedForm_eq_word M t hF st B hk span pub) (seedForest M t hF st B hk span pub) v).le.trans
    (leaf_resources M t hF st B hk span pub v.1 v.2)

/-- The native directory charges the trace surcharge exactly on cursor zero.
All other original leaves are covered by their actual incident words. -/
theorem billed_resources (i : Fin (q+1)) (L : Lane (q+1)) :
    ((seedWordForest M t hF st B hk span pub) (i,L)).resources ≤
      1+(seedWordLayout M t hF st B hk span).ports.halfBits (i,L)+
        (if i=0 then seedTraceWork low (TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells B.cursorCopies ((q+1)+low) else 0) := by
  by_cases first : i=0
  · rw [ite_eq_left first]
    have cap := seedWordForest_resources M t hF st B hk span pub (i,L)
    exact cap.trans (Nat.le_add_left _ _)
  · simp only [ite_eq_right first,Nat.add_zero]
    apply (cast_resource (seedForm_eq_word M t hF st B hk span pub) (seedForest M t hF st B hk span pub) (i,L)).le.trans
    rw [relay_charge M t hF st B hk span pub i L first]
    let I := bitIndex hF t.width t.labels base st t.header t.time r k t.grid L
    have cap := I.relay_resources_le (r:=B.cursorCopies) i
    have width := B.cursor_half_width hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells (seedExt T low) (seedPin span low) (i,L)
    change (B.cursorCopies+1)*2*I.t+(B.cursorCopies+1)*2*I.t =
      (seedWordLayout M t hF st B hk span).ports.halfBits (i,L) at width
    rw [I.relay_resources] at cap
    change 1+(B.cursorCopies+1)*2*I.t+I.t ≤ 1+(seedWordLayout M t hF st B hk span).ports.halfBits (i,L)
    calc
      _ ≤ 1+2*((B.cursorCopies+1)*2*I.t) := cap
      _ = _ := congrArg (1 + ·) ((two_mul _).trans width)

/-- The only external inputs of the compiled root form are precisely the two
bits for each free endpoint coordinate. -/
theorem seed_ext_total (extent : 2*T≤S) : (∑ v : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).Site, seedExt T low v)=2*T := by
  have cover : T≤2^(q+1)*2^low := by
    have grid := t.grid
    rw [pow_add,pow_one,pow_add] at grid
    omega
  change (∑ v : Fin (q+1)×Lane (q+1), seedExt T low v)=_
  rw [Fintype.sum_prod_type]
  simp only [seedExt]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact ((finFunctionFinEquiv (m:=2) (n:=q+1)).sum_comp (fun l => retained T low l.val)).trans (retained_total cover)

end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor LaneCursor.RowLayout TraceSuffix TraceSourceOwner HistoryContraction
open scoped BigOperators Classical
variable {F : Type} [Field F] [Fintype F] {w p r k S base f q low T : ℕ}
    (M : Machine w p r k) (t : NativeTrace.Fits M S base ((q+1)+low) f)
    (hF : Fintype.card F≤2^w) (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
variable (extent : 2*T≤S) (pub : ℕ→Bool)

/-- Native seed rows carry two addresses for each of the real interval's clipped pairs. -/
theorem seed_ext_clipped (x : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).Site) :
    (seedWordLayout M t hF st B hk extent).ext x=2*B.clippedPairs hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells T x := by
  rcases x with ⟨i,L⟩
  let lane := (finFunctionFinEquiv L).val
  let row := i.val*2^(q+1)+lane
  have fit : lane<2^(q+1) := (finFunctionFinEquiv L).isLt
  change (if i=0 then 2*min (2^low) (T-lane*2^low) else 0) =
    2*(if row<2^(q+1) then min (T-row*2^low) (2^low) else 0)
  by_cases first : i=0
  · have atLane : row=lane := by simp [row,first]
    rw [ite_eq_left first,atLane,ite_eq_left fit,Nat.min_comm (2^low)]
  · have one : (1 : ℕ) ≤ i.val := Nat.pos_of_ne_zero (fun eq => first (Fin.ext eq))
    have large : 2^(q+1) ≤ i.val * 2^(q+1) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^(q+1)) one
    have late : ¬ row < 2^(q+1) := by
      exact Nat.not_lt.mpr (large.trans (Nat.le_add_right _ _))
    simp only [ite_eq_right first,ite_eq_right late,Nat.mul_zero]

/-- The all-history admission induction starts from the actual physical word forest
and the same unscaled cursor charge as the S43 scan. -/
theorem typed_seed_charge (x : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).Site) :
    1+(B.cursorState hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).incidentWidth x≤(B.seedWork hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells T B.cursorCopies ((q+1)+low) (TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) x ∧ (seedWordLayout M t hF st B hk extent).ports.form.width x≤2*(B.seedWork hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells T B.cursorCopies ((q+1)+low) (TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) x ∧
      ((seedWordForest M t hF st B hk extent pub) x).resources≤(B.seedWork hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells T B.cursorCopies ((q+1)+low) (TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) x := by
  rcases x with ⟨i,L⟩
  let slots := (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells
  let off := 1+(((q+1)+low)+((q+1)+low))
  let addr := (TraceSourceOwner.shape w p r k S f ((q+1)+low)
    (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride
  let A := B.cursorState hk low off slots
  let word := seedWordLayout M t hF st B hk extent
  let cost := B.seedWork hk low off slots T B.cursorCopies ((q+1)+low) addr slots (i,L)
  let clipped := B.clippedPairs hk low off slots T (i,L)
  let half := A.incidentWidth (i,L)
  have halves : word.ports.halfBits (i,L)=half := A.words_incidentWidth word (i,L)
  have floor : 1+half+clipped≤cost :=
    B.seedWork_covers hk low off slots T B.cursorCopies ((q+1)+low) addr slots (i,L)
  have wid : word.ports.form.width (i,L)=2*clipped+half :=
    congrArg₂ Nat.add (seed_ext_clipped M t hF st B hk extent (i,L)) halves
  change 1+half≤cost ∧ word.ports.form.width (i,L)≤2*cost ∧ _
  refine ⟨by omega,by omega,?_⟩
  let bill := seedTraceWork low addr slots B.cursorCopies ((q+1)+low)
  have earned : ((seedWordForest M t hF st B hk extent pub) (i,L)).resources ≤
      1+word.ports.halfBits (i,L)+(if i=0 then bill else 0) :=
    billed_resources M t hF st B hk extent pub i L
  apply earned.trans
  rw [halves]
  let lane := (finFunctionFinEquiv L).val
  let row := i.val*2^(q+1)+lane
  change 1+half+(if i=0 then bill else 0) ≤
    1+(half+(if row<2^(q+1) then min (T-row*2^low) (2^low)+bill else 0))
  by_cases first : i=0
  · have atLane : row=lane := by simp [row,first]
    have early : row<2^(q+1) := by rw [atLane];exact (finFunctionFinEquiv L).isLt
    rw [ite_eq_left first,ite_eq_left early,Nat.add_assoc]
    exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_add_left _ _) half) 1
  · rw [ite_eq_right first,Nat.add_zero]
    exact Nat.add_le_add_left (Nat.le_add_right _ _) 1

/-- The same S43 seed charge pays the real trace table, both physical endpoint
words of each clipped pair, and at least one visit, including relay-only rows. -/
theorem native_seed_amount (i : Fin (q+1)) (L : Lane (q+1)) :
    1≤(B.seedWork hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells T B.cursorCopies ((q+1)+low) (TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) (i,L) ∧
    (cursorAtom M t hF st B.cursorCopies T extent pub i L).table.cells≤(B.seedWork hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells T B.cursorCopies ((q+1)+low) (TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) (i,L) ∧
    seedExt T low (i,L)≤2*(B.seedWork hk low (1+(((q+1)+low)+((q+1)+low))) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells T B.cursorCopies ((q+1)+low) (TraceSourceOwner.shape w p r k S f ((q+1)+low) (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).internal).stride (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) (i,L) := by
  let atom := cursorAtom M t hF st B.cursorCopies T extent pub i L
  have charged := typed_seed_charge M t hF st B hk extent pub (i,L)
  have stored : ((seedWordForest M t hF st B hk extent pub) (i,L)).resources =
      atom.table.internal+atom.table.cells+1 :=
    cast_resource (seedForm_eq_word M t hF st B hk extent pub)
      (seedForest M t hF st B hk extent pub) (i,L)
  have paid := stored.ge.trans charged.2.2
  have span := charged.2.1
  change seedExt T low (i,L)+(seedWordLayout M t hF st B hk extent).ports.halfBits (i,L) ≤ _ at span
  exact ⟨by omega,by change atom.table.cells≤_;omega,by omega⟩


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
