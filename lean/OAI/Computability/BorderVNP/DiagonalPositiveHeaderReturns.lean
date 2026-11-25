import OAI.Computability.BorderVNP.DiagonalPositiveHeaderInstalled
import OAI.Computability.BorderVNP.CubeScatterTransmissionRecovery

/-! # Per-execution physical header inversion, including zero-valued continuations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator ProcessorSlots Routing JointHeader

variable {R r t d link inner n w reserve axes groups cap dim tally : ℕ} {Edge : Type}
variable {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool} {ext : Exterior R r link → Bool}
variable {L : WireLayout (R+1) r link}
local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally

/-- The actual initial reference word of a team is the bit in that very team's
reference-partner block. This read precedes all local path weights. -/
theorem modeTag_observed (args : Fin (R+1) → UnitAddresses) (u : Fin (R+1)) (hw : 0<w)
    {base : ℕ} (fit : (G.transferFrame u (args u).header (args u).dst).Fits w base)
    (size : (args u).header = L.header) :
    ∃ (block : Block (R+1)) (positive : 0<L.header),
      modeTag (w:=w) G args pin ext u = ((L.exteriorEquiv ext).broadcast block ⟨0,positive⟩).toNat := by
  let f := G.transferFrame u (args u).header (args u).dst
  obtain ⟨ne,lt⟩ := f.partner_spec L.three
  let v : Fin (R+1) := ⟨f.partner,lt⟩
  have diff : u ≠ v := fun eq => ne (congrArg Fin.val eq.symm)
  let a := args u
  let F := G.processorFields u pin ext a.ibase a.hbase a.starbase
  have bound := fit.branch.trans_eq size
  exact ⟨blockOf u v diff,bound,G.read_message_header L u v diff pin ext a.ibase a.hbase a.starbase
    (processorMemory F w) (F.containsInput_initial w) hw ⟨0,bound⟩⟩

/-- Every collection of actual returning header copies on the positive branch has
one parse. The conclusion is per execution and also applies to a zero-valued
residue continuation or to opposing signs elsewhere in the same coefficient. -/
theorem positive_prefix_parsed (header : ReturnedHeaders G pin ext L w) (args : Fin (R+1) → UnitAddresses)
    (u : Fin (R+1)) (base : ℕ) (hw : 0 < w) (fit : (G.transferFrame u (args u).header (args u).dst).Fits w base)
    (size : (args u).header = L.header) (positive : modeTag (w:=w) G args pin ext u ≠ 0)
    (exactWidth : L.header = PositiveFields.width reserve axes groups cap (R+1) dim tally) :
    ∃! p : Fields, (∀ block, JointHeader.observed L ext block = p.bits) ∧
      ∀ i, let m := (header.returned i).val.2.2
        FlatAt m (header.dest i) p.bits ∧ PackedHistoryCircuit.profileRAM m (header.dest i) = p.profile ∧
        FlatAt m (header.dest i+1+reserve) (Cube.DeclarationBits.spelling p.cube) ∧
        DiagonalTallyBits.WordsAt m (header.dest i+1+reserve+Cube.DeclarationBits.length axes groups cap) p.tallyWords := by
  obtain ⟨fixed,room,bit⟩ := modeTag_observed (G:=G) (pin:=pin) (ext:=ext) args u hw fit size
  have on : (L.exteriorEquiv ext).broadcast fixed ⟨0,room⟩ = true := by
    cases z : (L.exteriorEquiv ext).broadcast fixed ⟨0,room⟩ with
    | false => exact (positive (bit.trans (congrArg Bool.toNat z))).elim
    | true => rfl
  have tag : (JointHeader.observed L ext fixed).head? = some true := by
    change (List.ofFn ((L.exteriorEquiv ext).broadcast fixed)).head? = some true
    rw [List.head?_eq_some_head (by simp [room.ne']),List.head_ofFn]
    exact congrArg some on
  obtain ⟨common,copied⟩ := JointHeader.observed_of_returns fixed header.ibase header.hbase header.starbase header.dest
    header.args header.macros header.regs header.input hw header.physical header.resident header.room header.returned
  obtain ⟨p,parse,unique⟩ := PositiveFields.unique_parse (JointHeader.observed L ext fixed)
    ((JointHeader.observed_length ..).trans exactWidth) tag
  refine ⟨p,⟨fun b => (congrArg List.ofFn (broadcast_eq common b fixed)).trans parse.symm,?_⟩,?_⟩
  · intro i m
    have read : FlatAt m (header.dest i) p.bits := parse.symm ▸ copied i
    exact ⟨read,p.copied hw read⟩
  · intro q h
    exact unique q (h.1 fixed).symm

end TeamContraction

end BorderVNP
end Computability
end OAI
