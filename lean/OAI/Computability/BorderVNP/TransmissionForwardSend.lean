import OAI.Computability.BorderVNP.TransmissionSenderHop

/-! # Every genuine data comparison passes on the exterior assigned to the expansion term -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → ℕ} {origin stride : ℕ}

private theorem not_sender_of_shared (a : Range w) (team : Word w) (tag : a.kind = 0) :
    a.selected team ≠ some (some .sendData) := by
  simp (config := {decide := true}) only [Range.selected,decision,Decision.role,Range.bank,tag]
  split_ifs <;> simp_all

/-- In every reached sender comparison the literal/substituted input and the
routed physical word agree with the assigned record payload. Both read addresses
are protected by every earlier store, for arbitrary locally shared guesses. -/
theorem TransferBank.assigned_senders {u : Fin (R+1)} (A : TransferBank G pin ext L.width w L.header u)
    {tab : TableLayout} {row : ℕ → TableRow} {before : Memory w} (teams : R+1 = tab.teams)
    (widths : L.width = tableWidth tab row teams) (al : tab.Allocated w) (fit : tab.RowsFit w row)
    (base : (A.pub 0).val = tab.frame) (fields : tab.frameFields (readings before))
    (records : tab.recordsMatch row (readings before)) (im : tab.Image row (readings before) (readings A.mem))
    (written : WrittenPlacement tab row before A.pub D pp lp owner origin stride (G.pinLayout u A.ibase A.hbase A.starbase))
    (_inputRoom : (G.processorFields u pin ext A.ibase A.hbase A.starbase).header.length ≤ origin)
    (guess : Fin (R+1) → ℕ → Bool) (shared : Fin tab.count → ℕ → Bool)
    (sub : Pins.SubstitutionAt (G.pinLayout u A.ibase A.hbase A.starbase) (guess u) A.mem)
    {fixed : Block (R+1)} {header : Fin L.header → Bool} {high : Fin (R+1) → Fin (R+1) → ℕ → Bool}
    (checks : Checks L.three L.width fixed header high (tab.recordPayload row (G.assignedRows guess D pp lp shared))
      (L.exteriorEquiv ext)) :
    let rows := tableRange tab A.mem
    let team := directoryFrame A.pub A.mem 0
    SendersMatch rows A.pub A.mem ∧ ∀ k < (directoryFrame A.pub A.mem 13).val,
      (rows k).selected team = some (some .sendData) → ∀ j < (rows k).width.val, ∀ i < k,
        (rows i).protectsCell team ((rows k).source.val+j) ∧ (rows i).protectsCell team ((rows k).senderAddress A.pub A.mem j) := by
  let rows := tableRange tab A.mem
  let team := directoryFrame A.pub A.mem 0
  have count := image_count im al A.pub base fields
  obtain ⟨cols,sources⟩ := written.columns A.mem im
  have one (k : ℕ) (hk : k < (directoryFrame A.pub A.mem 13).val) (sel : (rows k).selected team = some (some .sendData))
      (j : ℕ) (hj : j < (rows k).width.val) :
      A.mem ((rows k).source.val+j) = A.mem ((rows k).senderAddress A.pub A.mem j) ∧
      ∀ i < k, (rows i).protectsCell team ((rows k).source.val+j) ∧ (rows i).protectsCell team ((rows k).senderAddress A.pub A.mem j) := by
    let idx : Fin tab.count := ⟨k,count ▸ hk⟩
    have data : k < (D.directory pp lp).length := by
      by_contra! earlier
      exact not_sender_of_shared _ _ (written.sharedTag A.mem im k earlier idx.isLt) sel
    let i : Fin (D.directory pp lp).length := ⟨k,data⟩
    let raw := (D.directory pp lp)[i.val]
    let a := rows k
    have hr : raw ∈ D.directory pp lp := List.getElem_mem i.isLt
    have src : a.source.val = raw.sourceBase (G.pinLayout u A.ibase A.hbase A.starbase) := sources.source i
    have ej : j < raw.width := (cols.width i) ▸ hj
    obtain ⟨hp,ho⟩ := D.populated_source_bounds pp lp hr written.positive ej
    have proc : D.processors = r := written.dimensions.1
    have lit : D.literal = G.program.length+t := written.dimensions.2
    have own : a.teamA.val = u.val := (congrArg Fin.val (a.sender_endpoints sel).1.symm).trans A.teamWord
    have fromTeam : raw.team = u.val := (sources.team i).symm.trans own
    have bits := G.read_dataBit guess u pin ext A.ibase A.hbase A.starbase A.mem A.physical sub raw fromTeam
      (proc ▸ hp) j (lit ▸ ho)
    let frame := G.transferFrame u L.header A.dst
    have span : ScheduledRange frame L.width a :=
      widths.symm ▸ ScheduledRange.of_table im al fit records frame teams idx.isLt
    obtain ⟨z,ne,p,peer,target,offset,addr,peek⟩ := A.sender_hop written.word a span sel hj
    obtain ⟨_,ha,hb,hw,hord⟩ := tableRange_fields im al records idx.isLt
    have first : (row idx).first = u.val := ha.symm.trans own
    have second : (row idx).second = z.val := hb.symm.trans peer
    have value := checks.hop_payload u _ p
    let pay := tab.recordPayload (N := R+1) row (G.assignedRows guess D pp lp shared)
    have off : p.2.val = tab.ordinal row idx+j := offset.trans (congrArg (·+j) hord)
    have rowVal := (congrArg (fun k => pay (min u p.1) (max u p.1) k) off).trans
      ((congrArg (fun peer => pay (min u peer) (max u peer) (tab.ordinal row idx+j)) target).trans
        (tab.recordPayload_eq row _ u z ne idx first second j (hw ▸ hj)))
    have assigned := value.trans rowVal
    rw [Wiring.assignedRows,dite_eq_left (show idx.val < (D.directory pp lp).length from data)] at assigned
    have matchWord : (A.mem (a.senderAddress A.pub A.mem j)).val = (G.dataBit guess raw j).toNat :=
      peek.trans (congrArg Bool.toNat assigned)
    constructor
    · change A.mem (a.source.val+j) = A.mem (a.senderAddress A.pub A.mem j)
      rw [src,bits]
      exact Fin.ext ((Nat.mod_eq_of_lt ((Bool.toNat_lt _).trans_le (Nat.one_lt_pow written.word.ne' (by decide : 1<2)))).trans matchWord.symm)
    · have sourceLow := D.source_below pp lp hr written.positive ej _ written.dimensions.1 written.dimensions.2 (tab.readExtent _)
          (tab.readExtent_bounds _).2.1 (tab.readExtent_bounds _).2.2
      intro k' hk'
      exact ⟨written.protects A.mem im k' (hk'.trans idx.isLt) team _ (src ▸ sourceLow),
        written.protects A.mem im k' (hk'.trans idx.isLt) team _ (addr.trans_le (by rw [Pins.ProcessorFields.header_length]; exact (tab.readExtent_bounds _).2.1))⟩
  exact ⟨fun k hk sel j hj => (one k hk sel j hj).1,fun k hk sel j hj => (one k hk sel j hj).2⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
