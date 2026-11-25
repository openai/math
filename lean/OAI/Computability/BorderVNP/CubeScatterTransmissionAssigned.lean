import OAI.Computability.BorderVNP.CubeScatterTransmissionPayload
import OAI.Computability.BorderVNP.TransmissionAssignedPayload

/-! # Reading an assigned cube payload back from the physical transmission

A prescribed strict-row word is scattered into the compact triangular
descriptor table. The chronological local guesses and the assigned exterior
supply complementary positions. Consequently the native pair-bank reads
recover that prescribed word on every row. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter
open private shared_info from OAI.Computability.BorderVNP.TransmissionPairViews

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}
variable {a q blocks K h : ℕ} {decl : LengthDeclaration a q}
variable {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

/-- Compact native table index of a strict physical symbol pair. -/
def sharedIndex (g : SharedRows.Layout) (p : Symbols q) := g.rowIndex p.val.1 p.val.2

private theorem sharedIndex_injective (g : SharedRows.Layout) : Function.Injective (sharedIndex (q := q) g) := by
  intro p v eq
  have h := g.rowIndex_inj p.property v.property eq
  exact Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2))

/-- The bit assignment for the compact shared records, extended by zero off the
actual rows and beyond the length of the provided word. -/
noncomputable def assignedShared (g : SharedRows.Layout) (raw : Symbols q → List Bool) : ℕ → ℕ → Bool :=
  Function.extend (sharedIndex g) (fun p j => ((raw p)[j]?).getD false) (fun _ _ => false)

/-- Each prescribed digit belongs to exactly one shared row of the native table. -/
theorem assignedShared_at (g : SharedRows.Layout) (raw : Symbols q → List Bool)
    (p : Symbols q) (j : ℕ) (inside : j < (raw p).length) :
    assignedShared g raw (sharedIndex g p) j = (raw p)[j] := by
  rw [assignedShared,(sharedIndex_injective g).extend_apply,List.getElem?_eq_getElem inside]
  rfl

private theorem receivedWord_at (m : Memory w) (base width j : ℕ) (hj : j < (receivedWord m base width).length) :
    (receivedWord m base width)[j] = decide ((m (base+j)).val = 1) := by
  simp only [receivedWord,List.getElem_ofFn]

/-- Replaying a prescribed complete chronological stream determines each
co-located bit at its actual table position. -/
private theorem TeamHistory.local_bit_of_choices (h : TeamHistory w) (bit : ℕ → ℕ → Bool)
    (stream : h.history.val.1.flatMap TeamRAM.Event.choices = tableChoiceBits h.rows h.team bit h.count)
    {i j : ℕ} (hi : i < h.count) (mode : (h.rows i).selected h.team = some (some .sharedHere))
    (hj : j < (h.rows i).width.val) : h.bits i j = bit i j := by
  have round : tableChoiceBits h.rows h.team h.bits h.count = List.ofFn h.word.val :=
    tableChoiceBits_decodeChoices h.rows h.team (List.ofFn h.word.val) (by simp)
  exact (tableChoiceBits_eq_iff_slot_eq h.rows h.team h.bits bit h.count).mp
    (round.trans (h.stream.symm.trans stream)) i hi mode j hj

/-- On the exterior assigned to these very data and shared words, the actual
forward pair-bank readback recovers all prescribed words. Co-located pairs use
the true native event stream, and remote pairs use the routed physical hop.
The criterion applies before any private scatter reads these buffers. -/
theorem SharedWriters.received_assigned (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (raw : Symbols q → List Bool) (lengths : ∀ p, (raw p).length = SharedRows.reserved blocks K h decl p)
    (dataCount : (D.directory pp lp).length = g.dataCount)
    (guess : Fin (R+1) → ℕ → Bool) {fixed : Block (R+1)} {header : Fin L.header → Bool}
    {high : Fin (R+1) → Fin (R+1) → ℕ → Bool}
    (checks : Checks L.three L.width fixed header high (f.table.recordPayload f.row
      (G.assignedRows guess D pp lp (fun i => assignedShared g raw i.val))) (L.exteriorEquiv ext))
    (streams : ∀ u, (H u).history.val.1.flatMap TeamRAM.Event.choices =
      tableChoiceBits (H u).rows (H u).team (assignedShared g raw) (H u).count) :
    f.receivedRows g group = raw := by
  funext p
  let u := group p.val.1
  let z := group p.val.2
  let a := p.val.1.val
  let b := p.val.2.val
  let i := sharedIndex g p
  have ab : a < b := p.property
  have bg : b < g.groups := frame.groups ▸ p.val.2.isLt
  have idx : i < f.table.count := writer.count ▸ g.index_lt ab bg
  obtain ⟨first,second,len,_,_⟩ := writer.declaredRows frame p
  apply List.ext_getElem (len.trans (lengths p).symm)
  intro j hj hraw
  have inside : j < (f.row i).width := by simpa only [ReturnedDelivery.receivedRows,receivedWord_length,i,sharedIndex] using hj
  apply (receivedWord_at (H u).history.val.2.2 (g.view a b) (f.row i).width j hj).trans
  have chosen := assignedShared_at g raw p j hraw
  by_cases eq : u = z
  · have ends : (f.row i).second = u.val := second.trans (congrArg Fin.val eq.symm)
    have digit := writer.local_digit u ab bg first ends inside
    obtain ⟨tag,ha,hb,hw,_,_⟩ := shared_info f g u (writer.emitted u) (writer.fitted u) writer.records writer.count ab bg
    let row := (H u).rows i
    have team : (H u).team = row.teamA := Fin.ext ((f.bank u).team.trans (ha.trans first).symm)
    have same : row.teamA = row.teamB := Fin.ext ((ha.trans first).trans (hb.trans ends).symm)
    have mode : row.selected (H u).team = some (some .sharedHere) := by
      change row.kind = 0 at tag
      rw [team]
      simp [Range.selected,Range.bank,decision,Decision.role,tag,same]
    exact digit.trans ((TeamHistory.local_bit_of_choices (H u) _ (streams u) ((f.fullCount u).symm ▸ idx) mode
      (hw.symm ▸ inside)).trans chosen)
  · obtain ⟨p',other,ordinal,digit⟩ := writer.remote_digit u z eq ab bg first second inside
    let pay := f.table.recordPayload (N := R+1) f.row
      (G.assignedRows guess D pp lp (fun k => assignedShared g raw k.val))
    have rowVal := (congrArg (fun k => pay (min u p'.1) (max u p'.1) k) ordinal).trans
      ((congrArg (fun peer => pay (min u peer) (max u peer) (f.table.ordinal f.row i+j)) other).trans
        (f.table.recordPayload_eq f.row _ u z eq ⟨i,idx⟩ first second j inside))
    have assigned := (checks.hop_payload u _ p').trans rowVal
    have shared : ¬i < (D.directory pp lp).length := by
      rw [dataCount]
      dsimp only [i,sharedIndex,SharedRows.Layout.rowIndex]
      omega
    change _ = G.assignedRows guess D pp lp (fun k => assignedShared g raw k.val) ⟨i,idx⟩ j at assigned
    rw [Wiring.assignedRows,dite_eq_right shared] at assigned
    exact digit.trans (assigned.trans chosen)

end TeamContraction

end BorderVNP
end Computability
end OAI
