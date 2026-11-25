import OAI.Hierarchy.GridChosenReceiverInstalledPrefix

namespace OAI
/-! # Reading an original evaluator input from its elected receiver slot -/

namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open GridScale GridThrough GridRegisteredSetting GridInstalledEvaluator GridReceiverDirectory FactorPinIntervals
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

private theorem source_bit {F : Type} [Field F] [Fintype F] {w k f e n tp tr tk ep er ek S B : ℕ}
    (X : Catalyst.Approximation F k f) (fc : FieldCode F (64*w)) (p : Fin n→Word (64*w))
    (tick : Machine (64*w) tp tr tk) (eval : Machine (64*w) ep er ek)
    (fit : e*2≤S) (x : GridDiagonal.Pins (Fin e)) (a : Fin S) :
    (pinSource (pairPorts (GridPinPublisher.exteriorRails fit))
      (GridPinCapturedSources.advice (e:=e) (compact:=B) X fc p tick eval) a).elim x id =
      GridSelfHeader.rawTape (B:=B) X fc p tick eval (x ∘ UniversalGrid.Wiring.railPin.symm) a.val := by
  let rail:=GridPinPublisher.exteriorRails fit
  by_cases low : a.val<e*2
  · let i : Fin (e*2):=⟨a.val,low⟩
    let ep:=UniversalGrid.Wiring.railPin.symm i
    have point : pairPorts rail ep=a := by
      apply Fin.ext
      change 2*ep.1.val+ep.2.toNat=a.val
      rw [←UniversalGrid.Wiring.railPin_val]
      change (UniversalGrid.Wiring.railPin (UniversalGrid.Wiring.railPin.symm i)).val=a.val
      rw [Equiv.apply_symm_apply]
    rw [(pinSource_inl _ _ a ep).2 point]
    simp only [Sum.elim_inl,GridSelfHeader.rawTape,GridDescription.input,dite_eq_left low]; rfl
  · have off : e*2≤a.val:=by omega
    have unused (u : Fin e×Bool) : pairPorts rail u≠a := by
      intro h
      have v:=congrArg Fin.val h
      change 2*u.1.val+u.2.toNat=a.val at v
      have ht:=u.1.isLt
      have side:=Bool.toNat_le u.2
      omega
    rw [pinSource_unused _ _ _ unused,Sum.elim_inr,id_eq]
    by_cases hi : a.val<GridSelfHeader.rawSize w e B n
    · rw [GridPinCapturedSources.advice,ite_eq_left ⟨off,hi⟩]
      exact (GridPinCapturedSources.true_bit X fc p tick eval (x ∘ UniversalGrid.Wiring.railPin.symm) a.val off).symm
    · rw [GridPinCapturedSources.unscattered X fc p tick eval a (.inr (by omega))]
      unfold GridSelfHeader.rawSize at hi
      simp only [GridSelfHeader.rawTape,GridDescription.input,dite_eq_right low,
        dite_eq_right (by omega : ¬a.val-e*2<w^2),GridSelfHeader.suffix,
        dite_eq_right (by omega : ¬a.val-e*2-w^2<B*w^2),
        dite_eq_right (by omega : ¬a.val-e*2-w^2-B*w^2<(n+GridReceiverHeader.count w)*(64*w))]

private theorem rail_room (d m n bank S : ℕ) (dimension : d = m)
    (external : 2 * ((d + 1) * GridIdleLayout.each d n bank) ≤ S) :
    GridControllerSimGeometry.railCount m n bank * 2 ≤ S := by
  subst m
  rw [Nat.mul_comm _ 2]
  exact external

variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}
    {blk : Block F} {m A w degree stageRate rootRate tariff power : ℕ}
    {v : TickSelection F (m+1) A w Q loss}
    (I : Installed blk m A w degree stageRate rootRate v)
    (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I tariff power)
local notation "l" => (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate)
local notation "arch" => GridDescription.capacity w
local notation "gate" => 26*GridDescription.sector w
local notation "W" => 64*w
local notation "rails" => GridControllerSimGeometry.railCount m (l).sideMinusOne (l).bank
variable (geom : ElectionRoom I.D (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate))
    (recv : Machine (64*w) (GridDescription.capacity w) (GridDescription.capacity w) (GridDescription.capacity w))
    (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace)
local notation "L" => streamLayout I R geom recv safe z
local notation "tbl" => GridNativeDispatch.actualTable I.D safe
local notation "sm" => GridNativeDispatch.selectorRoom I.D l R.table R.selector safe
local notation "widths" => (fun i=>(v.replacement.width_le_size i).trans v.size_le)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2800000 in
/-- Both exterior payloads and fixed original tape fields are recovered from
their own slots in this selected tick, including addresses in the zero tail. -/
theorem slot_payload (x : GridDiagonal.Pins (Fin rails)) (c : Cell (m+1) (l).sideMinusOne)
    (j : Fin v.copies) (a : Fin I.inputSize) (same : (L).tick a=(c,j)) :
    streamInput I recv 0 gate R.text (R.rooms recv 0 gate).choose widths (tbl).codes sm z x c j ((L).slot a).val =
      GridDescription.input (x ∘ UniversalGrid.Wiring.railPin.symm) (GridDescription.code (q:=w^2) recv I.D.machine)
        (GridNativeDispatch.source I.D l v.replacement 0 gate) a.val := by
  let sel:=InputWindow I.D l z safe sm
  let bounds:=(R.rooms recv 0 gate).choose sel z
  have fit : rails*2≤I.inputSize :=
    rail_room (l).dimension m (l).sideMinusOne (l).bank I.inputSize rfl bounds.external
  let port:=pairPorts (GridPinPublisher.exteriorRails fit)
  have paired (e : Fin rails) : (L).origin (port (e,true))=(L).origin (port (e,false)) := by
    have cap:=e.isLt
    exact (TraceDistribution.Physical.origin_pair I.D.block I.D.axesFit I.D.machine I.D.fit I.D.field I.D.state
      I.D.passes I.D.passesFit z.1 (I.D.ordinal z.1) e.val (by omega)).symm
  have rd:=PinAssignment.ofFactorIntervals_read L GridIdleLayout.direction port paired x a
  dsimp only at rd
  rw [same] at rd
  unfold streamInput
  rw [dite_eq_left ((L).slot a).isLt]
  exact rd.trans (source_bit v.replacement (FieldCode.ofCardLe I.D.field) (GridNativeDispatch.params I.D l 0 gate)
    recv I.D.machine fit x a)

end
end Hierarchy.GridChosenReceiver

end OAI
