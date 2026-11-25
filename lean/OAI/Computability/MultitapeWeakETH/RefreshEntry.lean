import OAI.Computability.MultitapeWeakETH.RefreshReadback
import OAI.Computability.MultitapeWeakETH.RefreshPackets
import OAI.Computability.MultitapeWeakETH.HistoryCapacity

/-! # The selected refresh map on the actual retained descriptor memory -/

namespace OAI.Computability.MultitapeWeakETH.RefreshOperands

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords PortRefresh MapCallWords PhaseRecipe PairSimulation LocalHistory NodeArguments
open RefreshMapOperands DescriptorSpace NewSlots MotifBlocks MotifConversion MotifSelector StackInterpreter
open private selected_widths from OAI.Computability.VPVNP.CompressorRefreshMapWorkspace
open private demand_bound from OAI.Computability.VPVNP.CompressorRecordRefreshBuild
open scoped Fin.CommRing
noncomputable section

set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

variable {A k : Type} [Codec A] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)

/-- With a tape program for the retained memory, a single polynomial program runs the
chosen refresh motif directly on the two packed node arguments. It returns the full
ordered list of coefficient names on acceptance. -/
theorem refresh_entry (read : A × Bits.Word → Bits.Word) (hr : Poly read)
    (number : (parameterData B.refresh).Entry → ℕ) :
    ∃ run : Query A → Option (List Tally), Poly run ∧ ∀ {w g : ℕ} (ctx : A) (L : Layout) (i n : ℕ)
      (X : State S.portExponent (S.portExponent+g))
      (choice : DyadicRefreshChoice (a₀:=S.degreeExponent 0) (g:=g) X S.graph hE hC B.refresh)
      (p : (X.Base × BitWord g) × Fin (2^S.portExponent))
      (old : X.network.Half (oldSite X p))
      (new : (dyadicRefreshNext X S.graph hE hC B.refresh S.port_order S.degree_bounds.2 choice).network.Half
        (promotedSites p)) (C : LevelRecipe.Context w) (cap : ℕ),
      let Y := dyadicRefreshNext X S.graph hE hC B.refresh S.port_order S.degree_bounds.2 choice
      let I := entryInput B X choice p old new
      let bs := packed X (oldSite X p) old
      let cs := packed Y (promotedSites p) new
      (∀ j : BurstRAM.Word w, read (ctx,wordBits j) = wordBits (C.memory j.val)) →
      RefreshPayloadHistory.Data B L i n X choice C.memory →
      C.state.val = levelStart L i → (C.pub 2).val = levelStart L (i+1) →
      (C.pub 0).val = (sites X.baseIndex (bitWordFinEquiv g) p).val → 2^g < 2^w →
      D < 2^w → X.maxWireWidth ≤ cap → Y.maxWireWidth ≤ cap → cap < 2^w →
      bs.length ≤ 2^w → cs.length ≤ 2^w →
      run (encode ctx C bs cs cap) = (runEntry B.refresh (fun _ => zero_lt_one) I.demand I.payload I.party
        (MotifEntry.demandBits tieSource tieTarget I.party I.demandBits)
        (mapHalf S.portSupply (fun _ => MotifEntry.inputBits) I.supplyBits)).1.map (List.map (tally ∘ number)) := by
  choose eval ep exec using compile_expr read hr
  obtain ⟨lookup,cost,correct⟩ := MotifFields.fixed_program B.refresh (fun _ => zero_lt_one) number
  refine ⟨fun q => lookup (arguments B eval q),(arguments_poly B eval ep).compose cost,?_⟩
  intro w g ctx L i n X choice p old new C cap Y I bs cs rd stored state succ site lanes degree ow nw fit ob nb
  let x := encode ctx C bs cs cap
  let widths := MapFrameFields.nominal I.demand I.payload
  have bounded : ∀ f, widths f ≤ cap := by
    rintro (⟨d,e⟩ | ⟨d,e⟩)
    · exact (demand_bound X p.1 e).trans ow
    · have h := ((selected_widths B X choice (p.1,e.1)).2 e.2).trans nw
      exact (Nat.le_add_right (I.payload e) (repetitions B.refresh I.demand*B.refresh.selectorBits)).trans h
  obtain ⟨port,sizes,addr⟩ := readback B L i n X choice p C ctx bs cs cap eval
    (fun e => exec e ctx C bs cs cap rd) stored state succ site lanes degree bounded (fun f => (bounded f).trans_lt fit)
  have positive : 0 < w := by
    by_contra! h
    rw [show w=0 by omega,pow_zero] at degree
    exact (Nat.two_pow_pos S.portExponent).not_ge (Nat.lt_one_iff.mp degree).le
  have bits := packets B X choice p old new positive ob nb eval x rfl port
    (fun e => sizes (.inl (false,e))) (fun e => sizes (.inr (false,e))) addr
  exact (congrArg lookup bits).trans (correct I)

end
end OAI.Computability.MultitapeWeakETH.RefreshOperands
