import OAI.Computability.MultitapeWeakETH.ShrinkSiteArguments
import OAI.Computability.MultitapeWeakETH.SupplyCoordinates

/-! # All incident supply bits of a selected shrinking map on tape -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments NativeGrid CompressorRecords
open DescriptorSpace PhaseRecipe ShrinkBlockInputs MapResidentRows MotifConversion
open NearSquareRoot.InterchangeAffineMask
open private eq_poly from OAI.Computability.NearSquareRoot.InterchangeROMAffineMask
open private publicWords from OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
open private layout supplyWidth from OAI.Computability.VPVNP.PairShrinkRoleMapWitness
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
theorem supply_programs :
    ∃ get : Bool × (Bool × Fin 4) → Q × Tally → Bits.Word, (∀ e, Poly (get e)) ∧ ∀ {g w : ℕ} (ctx : D)
      (z : SiteArguments B i g) (d : Level w) (j : z.Row),
      let arg := z.input j
      let q := z.query d ctx j
      z.Ready d → (∀ p : Word w, read (ctx,wordBits p) = wordBits (d.memory p.val)) →
      (∀ e (h : arg.party=supply.src e), get (false,e) (q,tally (supplyWidths B.shrink arg.demand arg.payload e)) =
        List.ofFn (MotifEntry.inputBits (arg.supplyBits.1 e h))) ∧
      (∀ e (h : arg.party=supply.dst e), get (true,e) (q,tally (supplyWidths B.shrink arg.demand arg.payload e)) =
        List.ofFn (MotifEntry.inputBits (arg.supplyBits.2 e h))) := by
  let packet (ctx : Buffers D) := ctx.1.2
  let bank (ctx : Buffers D) := ctx.2
  have pp : Poly packet := by unfold packet; fun_prop
  have bp : Poly bank := Easy.snd.poly
  choose live lc lr using surviving_program B i (external read) (external_poly hr) packet pp
  choose shared sc sr using shared_program B i (external read) (external_poly hr) bank bp
  obtain ⟨sideWord,wc,wr⟩ := ShrinkHidden.expression (external read) (external_poly hr) (.header 38)
  let test (l : Bool) (q : Q) := eqWord (sideWord q,Carry.born l.toNat)
  have tc (l : Bool) : Poly (test l) := (wc.pair (Code.Poly.const _)).compose eq_poly
  let get (s : Bool × (Bool × Fin 4)) (u : Q × Tally) :=
    bif test s.2.1 u.1 then live s.1 s.2.2 u else shared s.2.2 u.1
  refine ⟨get,fun s => Poly.choose (Easy.fst.poly.compose (tc s.2.1)) (lc s.1 s.2.2) (Easy.fst.poly.compose (sc s.2.2)),?_⟩
  intro g w ctx z d j arg q ready rd
  let native := (order z.state (layoutOf(z)) z.owner).entries j
  let m := native.val.1
  let widths := ShrinkPreparedCall.width B.shrink z.state z.choice
  let profile := subdivisions (2^(a i)) (Shrink.colors (a i)) (2^(b i))
  let bits dir e := get (dir,e) (q,tally (widths m e))
  have raw := wr (z.buffers ctx w) (d.head B) (d.n*d.n) (siteIndex z.state z.owner).val j.val d.memory rd
  have flag : Bits.value (sideWord q) = (layoutOf(z)).toNat := by
    change Bits.value (sideWord (ShrinkHidden.query (z.buffers ctx w) (d.head B) (d.n*d.n) (siteIndex z.state z.owner).val,tally j.val)) = (layoutOf(z)).toNat
    rw [raw,value_native]
    have word : Expr.eval (publicWords (siteIndex z.state z.owner).val j.val) (d.head B) d.memory (.header 38) =
        ((layoutOf(z)).toNat : Word w) := ready.data.words.level.layout
    rw [word,Fin.val_cast_of_lt (by have := ready.data.words.oldRoom; have := Bool.toNat_le (layoutOf(z)); omega)]
  have yes : test (layoutOf(z)) q = true := (eqWord_true ..).mpr (flag.trans (Carry.birthValue _).symm)
  have no : test (!(layoutOf(z))) q = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have clash := (eqWord_true ..).mp hh
    rw [flag,Carry.birthValue] at clash
    have distinct (b : Bool) : b.toNat ≠ (!b).toNat := by cases b <;> decide
    exact distinct (layoutOf(z)) clash
  have useShared (dir : Bool) (t : Fin 4) : bits dir (!(layoutOf(z)),t) = shared t q := by
    change (bif test (!(layoutOf(z))) q then _ else shared t q) = _
    rw [no]
    rfl
  have useParent (dir : Bool) (t : Fin 4) :
      bits dir ((layoutOf(z)),t) = live dir t (q,tally (widths m ((layoutOf(z)),t))) := by
    change (bif test (layoutOf(z)) q then live dir t _ else _) = _
    rw [yes]
    rfl
  have widthFit (t : Fin 4) : widths m ((layoutOf(z)),t) ≤ 2^w := by
    have bound := z.state.packingData.shrinkTerm_bounds (State.two_le_packingColors _) (Nat.two_pow_pos _)
      z.state.shrinkNumber z.state.packingWidth (fun _ => z.state.width_le_maxWireWidth _) B.shrink m (z.choice m)
    exact ((bound.2 ((layoutOf(z)),t)).2.trans ready.factor).trans (z.space d ready).2.2.2.2.le
  let idx := z.state.shrinkStateIndex (S.shrink i) (layoutOf(z))
  have co := supply_coordinates (a:=a i) (b:=b i) (g:=g) z.state (layoutOf(z)) profile widths idx (S.shrink i).count_pos
  have atRow := co native.val.1 native.val.2 z.owner native.property.symm
  have atHidden := atRow z.hidden
  dsimp (config := {zeta := false}) only [profile,widths,ShrinkPreparedCall.width,SelectedFinish.chosen,
    PackingData.shrinkTermLayout,PackingData.termWidths,idx] at atHidden
  have coords := atHidden z.parent bits
  specialize coords ?_ ?_
  · intro dir t hit own
    have ans := sr t (z.buffers ctx w) z.state z.choice d.base d.positions d.blocks d.n d.cur (d.n*d.n) d.memory z.owner j
      widths z.hidden own rd ready.data rfl
    have branch := useShared dir t
    dsimp only [q,SiteArguments.query,Level.head,m,native,rowMotif,MapResidentRows.entry,
      SelectedFinish.chosen,PackingData.shrinkTermLayout,widths,ShrinkPreparedCall.width] at branch ans ⊢
    have result := branch.trans ans
    exact result
  · intro dir t hit own
    let Y := z.state.shrinkNext B.shrink (S.shrink i) z.choice
    let u := ShrinkSurvivingOperands.site z.state (layoutOf(z)) m t dir
    let parent : Y.network.Half u := atSite own z.parent
    have bound := (packed_length_le Y u parent).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ ready.nextDegree) ready.nextWidth)
    have fit := widthFit t
    dsimp only [widths,m,native,ShrinkPreparedCall.width] at fit
    have liveAt := lr dir t (z.buffers ctx w) z.state z.choice d.base d.positions d.blocks d.n d.cur (d.n*d.n) d.memory z.owner j
      parent rd ready.data (packed_atSite Y own z.parent).symm bound (bound.trans (z.space d ready).2.1.le)
    dsimp only [rowMotif,MapResidentRows.entry,ShrinkSlots.branchWidth] at liveAt
    have ans := liveAt fit
    have branch := useParent dir t
    dsimp only [q,SiteArguments.query,Level.head,m,native,rowMotif,MapResidentRows.entry,
      SelectedFinish.chosen,PackingData.shrinkTermLayout,widths,ShrinkPreparedCall.width,idx,profile,parent,u,Y] at branch ans ⊢
    have result := branch.trans ans
    exact result

  dsimp +instances only [arg,SiteArguments.input,ShrinkRole.MapWitness.input,bits,native,profile,widths,m,
    idx,ShrinkRole.MapWitness.rowEquiv,Equiv.trans_apply,Equiv.subtypeEquivRight_apply,
    a,MapResidentRows.Site,SelectedFinish.chosen,layout,ShrinkRole.MapWitness.instDecidableEqBase,Classical.decEq] at coords ⊢
  delta b Shrink.colors ShrinkPreparedCall.width supplyWidth MotifSelector.Word PackingData.shrinkSupplyWidths at coords ⊢
  delta a MapResidentRows.Site SelectedFinish.chosen layout ShrinkRole.MapWitness.instDecidableEqBase
    Classical.decEq Shrink.J PackingData.shrinkTermLayout at coords ⊢
  exact coords

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
