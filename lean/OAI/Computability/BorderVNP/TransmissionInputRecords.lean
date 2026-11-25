import OAI.Computability.BorderVNP.TransmissionInputParser

/-! # Physical initialization records emitted from the actual signed contraction tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP UniversalMachine BurstRAM RAMSerialization RAMTape TeamTapeInput
open private emitPort_inj from OAI.Computability.BorderVNP.TeamTapeInputLayout

variable {R r a inner : ℕ} {Edge : Type}

/-- Parsing and then emitting at the assigned global starting address gives
the true time-zero read/write halves of this processor's complete row, while
leaving its interior links available for the sorting network. -/
theorem tapeWiring_emit {w H start : ℕ} (hw : 2 ≤ w) (p : UniversalMachine.Program)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (interior : Fin r → Fin inner → Option Edge)
    (d link n : ℕ) (fit : 2*((programPrefix p).length+(cutWidth n+a))+R*link+inner ≤ n)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (int : Edge → Bool) (ibase hbase starbase : ℕ) (s : Stacks TeamTapeInputEmit.Port)
    (rs : List (WordRecord w)) (ready : TeamTapeInputEmit.Ready hw H start [] rs s) :
    let G := tapeWiring p free interior d link n fit
    let fields := G.processorFields u pin ext ibase hbase starbase
    let data := fields.row j
    let route := List.ofFn (fun i => (interior j i).elim false int)
    2*(start+data.length) ≤ 2^w → rs.length+2*data.length ≤ 4*H →
      ∃ k out, k ≤ 46*n+19+TeamTapeInputEmit.budget w data.length ∧
        parserAndEmitter.Runs k (Sum.elim (initial (List.ofFn (G.word pin ext int u j))) s) out ∧
        TeamTapeInputEmit.Ready hw H (start+data.length) []
          (rs ++ TeamTapeInputEmit.records w start data) (out ∘ emitPort) ∧
        out (.inl (.cut .incident)) = route := by
  intro G fields data route room cap
  obtain ⟨k,hk,read⟩ := tapeWiring_parse p free interior d link n fit u j pin ext int ibase hbase starbase
  let pad := List.replicate (n-(2*((programPrefix p).length+(cutWidth n+a))+R*link+inner)) false
  let post := loaded (programPrefix p)
    (List.ofFn (free u j) ++ (fields.exterior j).flatten ++ fields.pins j ++ route ++ pad) data route
  let mid : Stacks InitPort := Sum.elim post s
  have parse : (program.onPorts Sum.inl).Runs k
      (Sum.elim (initial (List.ofFn (G.word pin ext int u j))) s) mid := by
    apply program.runs_onPorts_framed Sum.inl_injective read
    · exact fun _ => rfl
    · exact fun _ => rfl
    · rintro (i | i) hi
      · exact (hi i rfl).elim
      · rfl
  have stage : TeamTapeInputEmit.Ready hw H start data rs (mid ∘ emitPort) :=
    ⟨rfl,ready.cursor,ready.buffer,ready.fields⟩
  obtain ⟨ticks, next, cost, emit, after⟩ := TeamTapeInputEmit.runs stage room cap
  let out := installStacks emitPort mid next
  have embed := TeamTapeInputEmit.program.runs_onPorts emitPort_inj mid emit
  have source : installStacks emitPort mid (mid ∘ emitPort) = mid :=
    installStacks_eq emitPort_inj mid _ (fun _ => rfl)
  rw [source] at embed
  have same : out ∘ emitPort = next := funext (installStacks_at emitPort_inj mid next)
  exact ⟨_,out,Nat.add_le_add hk cost,parse.followedBy embed,same ▸ after,
    installStacks_outside mid next (fun k => by cases k <;> simp [emitPort])⟩

/-- Public row starts coincide with the processor-stride addresses used in the RAM. -/
theorem processor_rowStart {L : RoutingISA.Pins.Layout} (F : RoutingISA.Pins.ProcessorFields L)
    (i : Fin L.processors) : TeamTapeInputEmit.rowStart F.row i = i.val * L.stride := by
  let rows := (List.ofFn F.row).take i.val
  have widths : rows.map List.length = rows.map (fun _ => L.stride) := by
    apply List.map_congr_left
    intro row hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hrow)
    exact F.row_length j
  change rows.flatten.length = _
  rw [List.length_flatten, widths, List.map_const']
  simp [rows]

/-- All per-processor records emitted at their assigned row starts give exactly the
chronological initialization of the same header used by the native live-pin proofs. -/
theorem Wiring.records_processorFields {R r t d link inner n : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (u : Fin (R+1)) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase w : ℕ) :
    let F := G.processorFields u pin ext ibase hbase starbase
    2*F.header.length ≤ 2^w →
      ((List.ofFn fun i : Fin r => TeamTapeInputEmit.records w (i.val * (G.pinLayout u ibase hbase starbase).stride) (F.row i)).flatten).map
        WordRecord.record = (TeamRecords.transcript (fun _ => 0)
          (TeamRecords.initialization F.header.length (TeamTapeInputEmit.headerWord w F.header))).flatMap
            TeamRecords.pair := by
  intro F room
  have result := TeamTapeInputEmit.rows_decode F.row room
  simp only [processor_rowStart] at result
  exact result

end TeamContraction

end BorderVNP
end Computability
end OAI
