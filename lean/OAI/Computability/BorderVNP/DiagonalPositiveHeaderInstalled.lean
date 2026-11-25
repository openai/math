import OAI.Computability.BorderVNP.DiagonalPositiveHeaderProfile

/-! # Positive header fields in every actual residual native evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Pins RoutingISA.Evaluator Routing JointHeader
open scoped BigOperators Classical

variable {R r d link n w reserve axes groups cap dim tally : ℕ}
local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally

/-- A nonzero native positive product has exactly one raw field tuple. Each team's
charged residual evaluator has these actual profile, cube and tally fields in RAM.
The allocation ends at the last subtotal bit. -/
theorem positive_product_parsed (physical : UniversalMachine.Program) {a e : ℕ} (eval : Code)
    (mac : TeamOpcode.Macros w 8) (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
    (fit : fitsWith physical 64 32 r w a R link n e) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (L : WireLayout (R+1) r link)
    (fixed : Block (R+1)) (hw : 0 < w) (width : ∀ u, (args u).header = L.header)
    (exactWidth : L.header = PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (he : eval.withoutAccept = true) :
    let P := (withStartup eval).program
    let G := wiringWith physical P (S.withPacket pack) d link n e fit
    let val := positiveMaskedNativeValue G eval mac S.publicWords S.registers args pin S.limit.val S.burst.val (n^25) ext
    (∀ u, (args u).Fitted G u (pack u) (S.publicWords u) (adviceOffsetWith physical r 32 64 w n)) →
    (∀ u, packetUnitBudget (args u).advice.count w (G.transferFrame u (args u).header (args u).dst)
      (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase) ≤ S.limit.val) →
    (∏ u, val u) ≠ 0 → ∃! p : Fields,
      (∀ block : Block (R+1), JointHeader.observed L ext block = p.bits) ∧
      ∀ u, let a := args u
        ∃ used bank mem, used ≤ jointBudget a.advice.count w+(G.transferFrame u a.header a.dst).readTicks+2 ∧
          (G.processorFields u pin ext a.ibase a.hbase a.starbase).ContainsInput mem ∧
          Frame (G.pinLayout u a.ibase a.hbase a.starbase) (readings (S.publicWords u)) (readings mem) ∧
          FlatAt mem a.dst p.bits ∧ PackedHistoryCircuit.profileRAM mem a.dst = p.profile ∧
          FlatAt mem (a.dst+1+reserve) (Cube.DeclarationBits.spelling p.cube) ∧
          DiagonalTallyBits.WordsAt mem (a.dst+1+reserve+Cube.DeclarationBits.length axes groups cap) p.tallyWords ∧
          val u = boundedValue eval (S.publicWords u) mac bank mem (S.limit.val-used) S.burst.val (n^25) := by
  intro P G val fitted time nonzero
  obtain ⟨common,tag,residual⟩ := positive_product_header physical eval mac S pack fit args pin ext L fixed hw width he
    fitted time nonzero
  let raw := JointHeader.observed L ext fixed
  obtain ⟨p,parse,unique⟩ := PositiveFields.unique_parse raw ((JointHeader.observed_length ..).trans exactWidth) tag
  refine ⟨p,⟨?_,?_⟩,?_⟩
  · intro block
    exact (congrArg List.ofFn ((common block).trans (JointHeader.observed_bits ..))).trans parse.symm
  · intro u a
    obtain ⟨used,bank,mem,cost,input,frame,copy,value⟩ := residual u
    have whole : FlatAt mem a.dst p.bits := parse.symm ▸ copy
    obtain ⟨profile,cube,tallies⟩ := p.copied hw whole
    exact ⟨used,bank,mem,cost,input,frame,whole,profile,cube,tallies,value⟩
  · intro q h
    exact unique q (h.1 fixed).symm

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
