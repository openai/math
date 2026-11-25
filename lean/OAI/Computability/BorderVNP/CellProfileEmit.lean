import OAI.Computability.BorderVNP.CellProfileEmitRows
import OAI.Computability.BorderVNP.CellEmitLists
import OAI.Computability.BorderVNP.CellRecordGuards

/-! # Complete native profile-record descriptor emission

The public record is represented by the five typed fields after its three tag
bits. Each static histogram entry and route is visited exactly once while
constructing the compact private generator input. Iterations over copies,
candidate counts and lanes belong to the emitted commands.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring ExactQuantumFactoring.BitStackProgram

variable {α : Type} {ea : α → List Bool}

/-- Emit the complete locally scoped profile checker from its dynamic physical fields. -/
noncomputable def profileProgram {c w : α → ℕ} {p : α → Port} {h : α → List ℕ} {rs : α → List Route}
    (hc : Procedure ea Nat.bits c) (hp : Procedure ea Typed.port p) (hw : Procedure ea unaryCode w)
    (hh : Procedure ea Typed.naturals h) (hr : Procedure ea (listCode Typed.route) rs) :
    Statement ea (fun x => profileRow (c x) (p x) (w x) (h x) (rs x)) := by
  let n := (NativeAIG.Emission.listUnaryLength Nat.bits 0).comp hh
  let nbin := Procedure.unaryToBits.comp n
  let size := profileAux hc nbin
  let range := profileRange size hc hp hw n
  let zero := Procedure.constant ea Nat.bits 0
  let ctx := Procedure.first ea (prodCode Nat.bits Nat.bits)
  let pair := Procedure.second ea (prodCode Nat.bits Nat.bits)
  let idx := (Procedure.first ..).comp pair
  let adv := (Procedure.second ..).comp pair
  let term := profileTerm (zero.comp ctx) (size.comp ctx) (hc.comp ctx) (hp.comp ctx) (hw.comp ctx) idx adv
  let terms := sequenceMapIdx (f := fun x t a => Profile.termGen 0 (Profile.auxSize (c x) (h x).length)
    (c x) (p x) (w x) t a) 0 hh term
  let ctx' := Procedure.first ea Typed.route
  let route := profileRoute (zero.comp ctx') (size.comp ctx') (hc.comp ctx') (hp.comp ctx')
    (hw.comp ctx') (nbin.comp ctx') (Procedure.second ea Typed.route)
  let routes := sequenceMap (f := fun x r => Profile.routeGen 0 (Profile.auxSize (c x) (h x).length)
    (c x) (p x) (w x) (h x).length r) (⟨0,0,⟨0,0,0⟩,⟨0,0,0⟩⟩ : Route) hr route
  exact scopedFlags size (seqStmt range (seqStmt terms routes))

/-- On the ordinary binary packet encoding the emitted width is clipped to the available
histogram length; all genuine crossing profiles satisfy this bound. -/
noncomputable def profilePacket : Statement ProfileData.code (fun x =>
    profileRow x.1 x.2.1 (min x.2.2.2.1.length x.2.2.1) x.2.2.2.1 x.2.2.2.2) := by
  let p := Procedure.identity ProfileData.code
  exact profileProgram (ProfileData.copies p) (ProfileData.selector p) (ProfileData.clippedWidth p)
    (ProfileData.histogram p) (ProfileData.routes p)

/-- For all well-formed source widths, the output is the exact serialization of the
original public profile record guard. No further public padding bits are required. -/
noncomputable def profileRecord {d : α → ProfileData.Data} (hd : Procedure ea ProfileData.code d)
    (boxes : α → List (List Factor)) (hw : ∀ x, (d x).2.2.1 ≤ (d x).2.2.2.1.length) :
    Statement ea (fun x => recordGuard (boxes x)
      (.profile (d x).1 (d x).2.1 (d x).2.2.1 (d x).2.2.2.1 (d x).2.2.2.2)) :=
  (profilePacket.comp hd).congrFun (fun x => by
    change CellMacro.Generator.serialized 8 (profileRow _ _ (min _ _) _ _) = _
    rw [min_eq_right (hw x)]
    rfl)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
