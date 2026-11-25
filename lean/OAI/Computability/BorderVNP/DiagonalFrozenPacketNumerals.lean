import OAI.Computability.BorderVNP.DiagonalFrozenPacketInputs
import OAI.Computability.BorderVNP.DiagonalSignedCountWordRoom
import OAI.Computability.BorderVNP.DiagonalSignedBundleBankRoom

/-! # Numerical operands of the selected signed cell-packet emitter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover Epoch TeamScales Packing DeckGrid Packing.Inherited FrozenTape
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open EnrichedOuter ExternalSew CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.LiveWords
open CellPacketGeometry.SiteWords CellSparse.Packet GeometryAdvice TerminalCells
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}

/-- The printed scalar widths of the signed packet on a chosen length. Here
`header` is the bit width used by the original opaque factor descriptors. -/
structure FrozenPacketNumerals (e : PaidIdentity K D m) (number : e.Entry → ℕ)
    (gadgets header word scalar mass : ℕ) : Prop where
  operands : scalar < 2^word
  counts : 15*mass+gadgets*word ≤ 2^word
  tags : ProgramSchemas.signedTagCapacity (e:=e) < 2^word
  paid : BoxRoster.paidWordLimit e < 2^word
  three : 3 < 2^word
  scalarIDs : ∀ t, number t < 2^word
  gadgetCount : gadgets < 2^word
  headerWidth : header < 2^word

variable {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- All scalar, record-operand and report-count budgets hold simultaneously
for the actual schedule, before choosing a candidate, frozen history or team.
The same assertion applies at every extension of the short history width. -/
theorem JointSchedule.eventually_frozen_packet_numerals (b : JointSchedule s E deg Q A B j)
    (headerFactor gadgets : ℕ) (number : e.Entry → ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let length := S.publicProgramFactor^(epochs s.τ n)*initialMass (D:=D) n r d (TeamScales.width n s.α) headerFactor
      let birth := max 2 (max (TeamScales.width n s.α) (seedBoxCapacity n r (Fintype.card (Cube D)) d
        (Fintype.card (Direction (Fintype.card (Cube D))))))
      let coefficient := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
      let scalar := max (15*length) (boundary S (d+1) (epochs s.τ n)).sites +
        max (max birth (coefficient*(length+1))) (max 1 (15*length))+1
      ∀ w ≥ 60*logWidth r n, FrozenPacketNumerals e number gadgets (headerFactor*logWidth r n) w scalar length := by
  filter_upwards [b.eventually_frozen_operand_room headerFactor number,
    b.eventually_signed_count_room headerFactor gadgets,
    eventually_ge_atTop (1+headerFactor+gadgets+ProgramSchemas.signedTagCapacity (e:=e))] with n fields counts hn
  intro r d length birth coefficient scalar w ext
  have hr : 1 ≤ r := stretch_one ..
  have nbits : n < 2^(logWidth r n) := Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r hr)
  have hc : 2^(logWidth r n) ≤ 2^w := Nat.pow_le_pow_right (by decide) (by omega)
  have kfit : headerFactor < 2^(logWidth r n) := by omega
  have header : headerFactor*logWidth r n < 2^w := by
    have hh : headerFactor*logWidth r n < 2^(logWidth r n)*2^(logWidth r n) :=
      Nat.mul_lt_mul_of_lt_of_le kfit Nat.lt_two_pow_self.le (Nat.two_pow_pos _)
    exact hh.trans_le (by rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨operand,paid,three,ids⟩ := fields w ext
  exact ⟨operand,counts w ext,by omega,paid,three,ids,by omega,header⟩

variable {start T cells live short native H E₁ A₁ hooks : ℕ}
    {seed : Format} {dir : Directory.Layout} {count : dir.entries=(fan S)^T*dir.sites}
    {number : e.Entry → ℕ} {scalar mass head : ℕ}

set_option maxRecDepth 5000 in
/-- The operands of the public ordered source, including the spare cell and
all printed paid lookup tables. The two address bounds use the actual
allocation of the complete frame containing the final bundle sort banks. -/
theorem SignedPacketInputBounds.emitter_words
    (input : SignedPacketInputBounds S start T cells live short native H E₁ A₁ hooks seed dir count number)
    (numbers : FrozenPacketNumerals e number hooks head native scalar mass)
    (pos : 0 < (boundaryShape S start T).sites) (fragments cables : ℕ)
    (fragmentCount : fragments=2*(boundaryShape S start T).edges+6*live)
    (cableCount : cables=(boundaryShape S start T).edges+4*live) :
    let boxes := scheduledBoxes dir count number pos
    let source := (ProgramSchemas.epoch S start short seed T).schema.append (Sewn.schema fragments short)
    let lastTape := FinalTies.tieSchema cables live native
    let cap := ProgramSchemas.signedTagCapacity (e:=e)
    let report := FinalReports.Spare.reports (C:=cells) (g:=hooks) (digits:=native) (E:=Fin dir.entries)
    let priv := FinalReports.Spare.priv (C:=cells) (g:=hooks) (digits:=native) (E:=Fin dir.entries)
    ∀ (sh : ∀ j, (source.tags j).length≤cap) (th : ∀ j, (lastTape.tags j).length≤cap),
      let tpl := template source lastTape boxes sh th priv report
      tpl.recordDepth ≤ native ∧ (∑ i, (boxes i).length)<2^native ∧
        source.rows.length+lastTape.rows.length<2^native ∧ cap<2^native ∧ 3<2^native ∧
        (∀ i v, v∈boxWords (boxes i) → v<2^native) ∧
        (∀ c, (report c).length < 2^native) ∧ (∀ c r, r ∈ report c → r.length<2^native) ∧
        ∀ fresh reserve gates depth,
          let ordinary := signedGridOutputCount cables cells dir.entries live 37
            (Total tpl.publicDepth tpl.chunkDepth)
          let outputs := ordinary+(2^depth+2^depth)
          let dest := Allocation.dest fresh reserve gates outputs native
          let start := Retained.packetBase dest cables cells dir.entries live 37
          Allocation.stop fresh reserve gates outputs native native < 2^native →
            start+2^tpl.publicDepth < 2^native ∧ 2^tpl.chunkDepth ≤ 2^native ∧ head < 2^native := by
  subst fragments cables
  let shape := boundaryShape S start T
  intro boxes source lastTape cap report priv sh th tpl
  obtain ⟨_,_,_,_,sh₀,th₀,small,_,length,_,_,records,_,_⟩ := input pos
  have rows : source.rows.length+lastTape.rows.length<2^native := by
    simp only [roster,List.length_append,List.length_map,List.length_finRange,List.length_cons,List.length_nil] at length
    change shape.sites+1+source.rows.length+lastTape.rows.length < 2^native at length
    omega
  have tags : tpl.recordDepth ≤ native := records
  have reportFit := FinalReports.Spare.packet_lengths (C:=cells) (E:=Fin dir.entries) numbers.gadgetCount
    (Nat.lt_two_pow_self (n:=native))
  refine ⟨tags, (scheduledBoxes_count dir count number pos).trans_lt small,
    rows,numbers.tags,numbers.three,scheduledBoxes_literal_words dir count number pos numbers.paid numbers.three numbers.scalarIDs,
    reportFit.1,reportFit.2,?_⟩
  intro fresh reserve gates depth ordinary outputs dest start stopped
  have address := Retained.signed_bundle_bank_room fresh reserve gates (shape.edges+4*live) cells dir.entries live
    tpl.publicDepth tpl.chunkDepth depth native native stopped
  exact ⟨address.2.2.2.2.2.2.1,address.2.2.2.2.2.2.2.1,numbers.headerWidth⟩

end Diagonal

end BorderVNP
end Computability
end OAI
