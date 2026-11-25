import OAI.Computability.MultitapeWeakETH.HistoryRefreshQuery
import OAI.Computability.MultitapeWeakETH.RefreshRole
import OAI.Computability.VPVNP.CompressorRefreshHookRetained

/-! # The refresh role at any selected occurrence in the actual chronological log -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression Compression.Refresh Compression.DegreeRefresh BurstRAM
open CompressorRecords DescriptorSpace PairSimulation LocalHistory NodeArguments DyadicBudget
open PortRefresh NewSlots RefreshMapOperands StackInterpreter TraversalRows TraversalRoles
open scoped Fin.CommRing
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)

private theorem ordinals_fit {w a g : ℕ} (X : State a (a+g)) (p : (X.Base × BitWord g) × Fin (2^a))
    (degree : 1 < 2^a) (fit : Fintype.card X.Base*2^a*2^g*2^a ≤ 2^w) :
    2^g < 2^w ∧ (NewSlots.sites X.baseIndex (bitWordFinEquiv g) p).val < 2^w := by
  let u := Fintype.card X.Base*2^a*2^g
  have : Nonempty X.Base := ⟨p.1.1⟩
  have pos := Fintype.card_pos (α:=X.Base)
  have block : 0 < Fintype.card X.Base*2^a := Nat.mul_pos pos (Nat.two_pow_pos _)
  have up : 2^g ≤ u := Nat.le_mul_of_pos_left _ block
  have grow : u < u*2^a := by
    simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left degree (Nat.mul_pos block (Nat.two_pow_pos _))
  exact ⟨up.trans_lt (grow.trans_le fit), (NewSlots.sites X.baseIndex (bitWordFinEquiv g) p).isLt.trans (grow.trans_le fit)⟩

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem history_refresh {hist : ℕ} (order : B.Entry ≃ Fin hist) (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ run : RefreshQuery → Option (List Tally), Poly run ∧ ∀ volume : Tally,
      let s := index (4*stepSize B) volume.length
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let u := stepSize B*s
      let X := source B s
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let L := gridLayout B volume
      let base := entryMemory B (3*u) u n s w
      let E := B.execute f hf s (lanes_fit B s) X
      1 ≤ s → slotDegree S ≤ s → ∀ (z : E.Choices) (log : CallProgram.Stores w),
        let past := executeLevels B f hf s (lanes_fit B s) X z
        let m := memory base log
        CompiledResident.resident B f hf 0 X.positions s n initial
          (Frame.data (k:=8) (BlockHeaderRun.header w L 0+6) base) past (E.finalState z) m →
        ∀ (i : Fin past.length) {g : ℕ} (Z : State S.portExponent (S.portExponent+g))
          (c : DyadicRefreshChoice (a₀:=S.degreeExponent 0) (g:=g) Z S.graph hE hC B.refresh)
          (selector : List Bool), (past[i.val]'i.isLt) = RefreshPlacement.selectedLevel B f hf Z c selector →
          ∀ (p : (Z.Base × BitWord g) × Fin (2^S.portExponent)) (old : Z.network.Half (oldSite Z p))
            (new : (dyadicRefreshNext Z S.graph hE hC B.refresh S.port_order S.degree_bounds.2 c).network.Half (promotedSites p)),
            let Y := dyadicRefreshNext Z S.graph hE hC B.refresh S.port_order S.degree_bounds.2 c
            let site := (NewSlots.sites Z.baseIndex (bitWordFinEquiv g) p).val
            run ((((volume,writes log),tally i.val),tally site),packed Z (oldSite Z p) old,packed Y (promotedSites p) new) =
              (TraversalPlan.emitted B order Z c p old new).map (List.map (tally ∘ Fin.val)) := by
  obtain ⟨read,hr,spec⟩ := descriptor_memory_program B
  let rd (q : LogQuery × Bits.Word) := read ((q.1.1,q.2),q.1.2)
  have rp : Poly rd := (((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)).poly.compose hr
  obtain ⟨run,cost,exec⟩ := RefreshOperands.refresh_role B order rd rp
  refine ⟨fun x => run (refreshQuery B x),(refreshQuery_poly B).compose cost,?_⟩
  intro volume s n w u X initial L base E hs hd z log past m resident i g Z c selector occurrence p old new Y site
  let v := past[i.val]'i.isLt
  have member : v ∈ executeLevels B f hf s (lanes_fit B s) X z := List.getElem_mem i.isLt
  have oldBound := (history_size hs z v member).2
  have newBound := (history_output_size hs z v member).2
  have oldDeg := v.oldDegree_le.trans (hd.trans (scale_ge B s))
  have newDeg := v.outputDegree_le.trans (hd.trans (scale_ge B s))
  change v = RefreshPlacement.selectedLevel B f hf Z c selector at occurrence
  rw [occurrence] at oldBound newBound oldDeg newDeg
  have stored := RefreshHookRetained.ofPast B f hf (0 : BurstRAM.Word w) X.positions s n Z c resident.2 i selector occurrence
  let ctx : LogQuery := (tally s,writes log)
  let C := refreshContext L i.val site m
  have sizes := ordinals_fit Z p S.port_order stored.sources.fits
  have natFit : n < 2^w := resident.1.2.1.startup.length ▸ (m (levelStart L 0+29)).isLt
  have prev : levelStart L i.val < 2^w := lt_of_le_of_lt (Nat.le_add_right ..) stored.sources.geometry.oldRoom
  have next : levelStart L (i.val+1) < 2^w := lt_of_le_of_lt (Nat.le_add_right ..) stored.sources.geometry.newRoom
  change run (refreshQuery B _) = _
  rw [refreshQuery_eq B volume i.val site _ _ log m]
  exact exec ctx L i.val n Z c p old new C n (spec s log) stored.sources
    (Nat.mod_eq_of_lt prev) (Nat.mod_eq_of_lt next) (Nat.mod_eq_of_lt sizes.2) sizes.1
    (oldDeg.trans_lt natFit) oldBound newBound natFit
    (packet_fits Z _ old oldDeg oldBound).le (packet_fits Y _ new newDeg newBound).le

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
