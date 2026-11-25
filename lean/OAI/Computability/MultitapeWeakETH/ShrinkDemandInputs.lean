import OAI.Computability.MultitapeWeakETH.ShrinkSiteArguments
import OAI.Computability.MultitapeWeakETH.DemandCoordinates

/-! # All incident demand bits of a selected shrinking map on tape -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments NativeGrid CompressorRecords
open DescriptorSpace PhaseRecipe ShrinkBlockInputs MapResidentRows
open private layout from OAI.Computability.VPVNP.PairShrinkRoleMapWitness
open scoped Classical Fin.CommRing
noncomputable section

set_option allowUnsafeReducibility true in
attribute [local reducible] Compression.PackingData.shrinkTermLayout
set_option allowUnsafeReducibility true in
attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout

variable {D k : Type} [Codec D] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  (read : D × Bits.Word → Bits.Word) (hr : Poly read)
local notation "layoutOf(" z ")" => SelectedFinish.chosen B (SiteArguments.state z) (SiteArguments.choice z)
local notation "Q" => ShrinkHidden.Indexed (Buffers D)

include hr in
set_option maxHeartbeats 2000000 in
theorem demand_programs :
    ∃ get : Bool × Bool → Q × Tally → Bits.Word, (∀ e, Poly (get e)) ∧ ∀ {g w : ℕ} (ctx : D)
      (z : SiteArguments B i g) (d : Level w) (j : z.Row),
      let arg := z.input j
      let q := z.query d ctx j
      z.Ready d → (∀ p : Word w, read (ctx,wordBits p) = wordBits (d.memory p.val)) →
      (∀ e (h : arg.party=demandSource e), get (false,e) (q,tally (arg.demand e)) =
        List.ofFn (MotifEntry.inputBits (arg.demandBits.1 e h))) ∧
      (∀ e (h : arg.party=demandTarget e), get (true,e) (q,tally (arg.demand e)) =
        List.ofFn (MotifEntry.inputBits (arg.demandBits.2 e h))) := by
  let bank (ctx : Buffers D) := ctx.1.1.2
  have bp : Poly bank := by unfold bank; fun_prop
  choose ab ac ar using ab_placed B i (external read) (external_poly hr) bank bp
  choose cd cc cr using cd_program B i (external read) (external_poly hr) bank bp
  let get (e : Bool × Bool) := if e.2 then cd e.1 else ab e.1
  refine ⟨get,fun e => ?_,?_⟩
  · rcases e with ⟨dir,_ | _⟩
    · exact ac dir
    · exact cc dir
  intro g w ctx z d j arg q ready rd
  let native := (order z.state (layoutOf(z)) z.owner).entries j
  let m := rowMotif z.state (layoutOf(z)) z.owner j
  let dem := z.state.packingData.shrinkDemandWidths z.state.shrinkNumber z.state.packingWidth m
  let old := ShrinkRole.MapWitness.placedOld B i z.state z.choice z.owner z.old
  let bits dir e := get (dir,e) (q,tally (dem e))
  obtain ⟨sites,frame,heap,_,cap⟩ := z.space d ready
  have width (e : Bool) : dem e ≤ d.n*d.n := (z.state.packingData.shrinkDemandWidths_le
    (State.two_le_packingColors _) (Nat.two_pow_pos _) z.state.shrinkNumber z.state.packingWidth
    (fun _ => z.state.width_le_maxWireWidth _) m e).trans (z.space d ready).2.2.2.1
  have fit : z.state.packingData.abWidth z.state.shrinkNumber z.state.packingWidth m ≤ 2^w := by
    have bound := (width false).trans cap.le
    exact bound
  have coords := demand_coordinates (a:=a i) (g:=g) z.state (layoutOf(z)) native.val.1 native.val.2 z.owner native.property.symm old bits
  specialize coords ?_ ?_ ?_
  · intro dir h
    have ans := ar dir (z.buffers ctx w) z.state z.choice d.base d.positions d.blocks d.n d.cur (d.n*d.n) d.memory z.owner j
      z.children z.old rd ready.data rfl sites frame heap ready.degree ready.width
    have equation := ans fit h
    dsimp only [bits,get,q,SiteArguments.query,Level.head,dem,PackingData.shrinkDemandWidths,
      demandWidths,m,native,rowMotif,MapResidentRows.entry,old] at equation ⊢
    simp only [Bool.false_eq_true,ite_false]
    exact equation
  · intro h
    have both := cr false (z.buffers ctx w) z.state z.choice d.base d.positions d.blocks d.n d.cur (d.n*d.n) d.memory z.owner j
      z.children z.old rd ready.data rfl sites frame heap ready.degree ready.width
    dsimp only [native,m,rowMotif,MapResidentRows.entry] at h both
    have equation := both.1 h rfl
    dsimp only [bits,get,q,SiteArguments.query,Level.head,dem,PackingData.shrinkDemandWidths,
      demandWidths,m,native,rowMotif,MapResidentRows.entry,old] at equation ⊢
    simp only [ite_true]
    exact equation
  · intro h
    have both := cr true (z.buffers ctx w) z.state z.choice d.base d.positions d.blocks d.n d.cur (d.n*d.n) d.memory z.owner j
      z.children z.old rd ready.data rfl sites frame heap ready.degree ready.width
    dsimp only [native,m,rowMotif,MapResidentRows.entry] at h both
    have equation := both.2 h rfl
    dsimp only [bits,get,q,SiteArguments.query,Level.head,dem,PackingData.shrinkDemandWidths,
      demandWidths,m,native,rowMotif,MapResidentRows.entry,old] at equation ⊢
    simp only [ite_true]
    exact equation

  dsimp +instances only [arg,SiteArguments.input,ShrinkRole.MapWitness.input,bits,dem,native,
    m,rowMotif,MapResidentRows.entry,old,ShrinkRole.MapWitness.rowEquiv,Equiv.trans_apply,Equiv.subtypeEquivRight_apply,
    a,MapResidentRows.Site,SelectedFinish.chosen,layout,ShrinkRole.MapWitness.instDecidableEqBase,Classical.decEq] at coords ⊢
  delta a MapResidentRows.Site SelectedFinish.chosen layout ShrinkRole.MapWitness.instDecidableEqBase
    Classical.decEq Shrink.J PackingData.shrinkTermLayout at coords ⊢
  exact coords

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
