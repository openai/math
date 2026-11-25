import OAI.Computability.BorderVNP.CubeScatterTransmissionRealization
import OAI.Computability.BorderVNP.CubeScatterTransmissionReverse
import OAI.Computability.BorderVNP.CubeScatterTransmissionLocalTape
import OAI.Computability.BorderVNP.CubeScatterTransmissionHeader
import OAI.Computability.BorderVNP.CubeScatterHopRecord

/-! # Recovering the whole exterior and every local route tape

The returned data and shared words identify every physical hop, including
the opposite leg through its native relay. The startup header copies and
routing padding checks account for every other bit of every exterior block.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {dst ib hb sb : Fin (R+1) → ℕ}
local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {a q blocks K h : ℕ}
variable {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

/-- Every exterior hop, with arbitrary block, orientation and ordinal, is the
bit of the appropriate recovered shared row or its genuine data source. -/
theorem SharedWriters.returned_hops {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H PL}
    (writer : SharedWriters f g src) (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (dataCount : (D.directory pp lp).length = g.dataCount) (guess : Fin (R+1) → ℕ → Bool)
    (sub : ∀ u, Pins.SubstitutionAt (PL u) (guess u) (H u).initial)
    (u v : Fin (R+1)) (p : Hop L.three L.width u v) :
    let value := G.assignedRows guess D pp lp (fun k : Fin f.table.count => assignedShared g (f.receivedRows g group) k.val)
    (L.exteriorEquiv ext).hop u v p = f.table.recordPayload f.row value (min u p.1) (max u p.1) p.2.val := by
  intro value
  obtain ⟨i,j,inside,ord,ends,code⟩ := f.table.hop_record f.row f.rowsFit f.teams f.widths value p
  exact (writer.returned_record_value frame dataCount guess sub p i j inside ends ord.symm).trans code.symm

/-- The genuine state at the start of the common header copies, and the actual
copy returns. This stage executes before the scheduler is populated. -/
structure ReturnedHeaders (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (L : WireLayout (R+1) r link) (w : ℕ) where
  /-- Base of the prepared substitution array at startup. -/
  ibase : Fin (R+1) → ℕ
  /-- Base of the installed signed header fields. -/
  hbase : Fin (R+1) → ℕ
  /-- Base of the packed reference input. -/
  starbase : Fin (R+1) → ℕ
  /-- Destination of the physical common-header copy. -/
  dest : Fin (R+1) → ℕ
  /-- Actual argument bank passed to each native header reader. -/
  args : Fin (R+1) → Arg → Word w
  /-- Team opcode macros available to the executing machine. -/
  macros : Fin (R+1) → TeamOpcode.Macros w 8
  /-- Registers on entry to the native header-copy routine. -/
  regs : Fin (R+1) → Bank w
  /-- RAM immediately before the native copy. -/
  input : Fin (R+1) → Memory w
  physical : ∀ u, (G.processorFields u pin ext (ibase u) (hbase u) (starbase u)).ContainsInput (input u)
  resident : ∀ u, (G.transferFrame u L.header (dest u)).At (readings (args u)) (readings (input u))
  room : ∀ u, (G.transferFrame u L.header (dest u)).Fits w (args u 0).val
  /-- The actual returning event trace and final registers and RAM. -/
  returned : ∀ u, Returns readBroadcast (args u) (macros u) (regs u) (input u)

variable {tab : TableLayout} {row : ℕ → TableRow} {pub : Fin (R+1) → Arg → Word w}
variable {before : Fin (R+1) → Memory w} {guess : Fin (R+1) → ℕ → Bool}

/-- From any actual family of returning native routes and header checks,
recover the unique exterior assigned to its shared words and forced deliveries.
The statement also recovers every full chronological local transmission tape
and the actual common header in every startup destination bank. -/
theorem SharedRoutePrepared.recover
    (input : SharedRoutePrepared G pin ext L D pp lp owner origin stride tab row pub before dst ib hb sb guess)
    (header : ReturnedHeaders G pin ext L w) (fixed : Block (R+1))
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (regs : Fin (R+1) → Bank w)
    (z : ∀ u, Returns route (pub u) (mac u) (regs u) (before u))
    (emitted : ∀ u, g.Emitted (src u) (readings (before u))) (fitted : ∀ u, g.Fits w (src u))
    (records : tab.records = g.records) (count : tab.count = g.dataCount+g.groups.choose 2)
    (dataCount : (D.directory pp lp).length = g.dataCount) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (frame : SymbolFrame g (src anchor) blocks K h decl group) :
    ∃ (H : Fin (R+1) → TeamHistory w) (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H PL),
      f.table = tab ∧ f.row = row ∧ SharedWriters f g src ∧
      ext = JointHeader.exterior L (JointHeader.observed L ext fixed) (JointHeader.observed_length ..)
        (f.table.recordPayload f.row (G.assignedRows guess D pp lp
          (fun k => assignedShared g (f.receivedRows g group) k.val))) ∧
      ∀ u, (H u).history.val.2 = (z u).val.2 ∧
        JointHeader.FlatAt (header.returned u).val.2.2 (header.dest u) (JointHeader.observed L ext fixed) ∧
        (z u).val.1.flatMap TeamRAM.Event.choices =
          tableChoiceBits (H u).rows (H u).team (assignedShared g (f.receivedRows g group)) (H u).count := by
  obtain ⟨H,f,ft,fr,fb,real⟩ := exists_delivery_of_routes tab row pub mac regs before _ z input.allocated input.ordered
    input.rowFit input.teams input.widths input.base input.fields input.records dst ib hb sb input.frame input.fit
    input.capacity input.physical input.inputBefore input.written
  let writer : SharedWriters f g src := ⟨fun u => fb ▸ emitted u,fitted,ft ▸ records,ft ▸ count,room⟩
  have sub (u : Fin (R+1)) : Pins.SubstitutionAt (PL u) (guess u) (H u).initial := by
    intro j hj
    have image := (real u).2.2.1
    change j < (G.pinLayout u (ib u) (hb u) (sb u)).count at hj
    have bound := input.subBefore u
    have eq := image.before_records input.ordered (by omega : ib u+j < tab.records)
    exact (Fin.ext eq).trans (input.substituted u j hj)
  let A u := TransferBank.ofScheduled (pub u) u (ib u) (hb u) (sb u) (dst u) input.teams input.widths
    (real u).2.2.1 input.allocated input.ordered (input.base u) (input.fields u) (input.frame u) (input.fit u)
    (input.capacity u) (input.physical u) (input.inputBefore u)
  have padding : ∀ k, (L.exteriorEquiv ext).padding k = false := by
    apply (transfer_padding_iff f.word A).mp
    intro u v diff
    have zero := (real u).2.2.2.2.2.2.2.1 v (fun eq => diff (Fin.ext eq.symm))
    change (G.transferFrame u L.header (dst u)).ZeroFrom (readings (H u).initial)
      ((G.transferFrame u L.header (dst u)).usedPrefix (input.fit u) L.width v) v
    rw [input.widths]
    exact zero
  obtain ⟨common,copied⟩ := JointHeader.observed_of_returns fixed header.ibase header.hbase header.starbase header.dest
    header.args header.macros header.regs header.input f.word header.physical header.resident header.room header.returned
  let pay := f.table.recordPayload (N := R+1) f.row (G.assignedRows guess D pp lp (fun k => assignedShared g (f.receivedRows g group) k.val))
  have check : Checks L.three L.width fixed (JointHeader.headerBits (JointHeader.observed L ext fixed)
      (JointHeader.observed_length ..)) (fun _ _ _ => false) pay (L.exteriorEquiv ext) :=
    ⟨common,(JointHeader.observed_bits ..).symm,fun u v p _ => writer.returned_hops frame dataCount guess sub u v p,
      fun u v p => ((f.relay v).relay_hop_iff f.word p).mp (f.checked u v p),padding⟩
  refine ⟨H,f,ft,fr,writer,(JointHeader.exterior_unique L fixed _ _ _ pay ext).mp check,?_⟩
  intro u
  exact ⟨(real u).1,copied u,(real u).2.1.symm.trans (writer.recovered_local_tape frame dataCount u)⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
