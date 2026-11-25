import OAI.Computability.BorderVNP.CubeISAOwnedScatterRealization
import OAI.Computability.BorderVNP.CubeISAOwnedRows
import OAI.Computability.BorderVNP.CubeISAOwnedVertexFold
import OAI.Computability.BorderVNP.CubeISAOwnedPacketFrame

/-! # Exact images and routed streams of an owned cube-packet row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA Physical Physical.Owned Physical.VertexIndex VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

/-- Inputs of the native callback along one strict symbol row. All per-packet fields refer to
the globally indexed physical packet. -/
structure PacketRowData (n d blocks b h K s : ℕ) where
  /-- Grouping coordinate. -/
  axis : Fin (n+1)
  /-- Increasing symbol pair of this row. -/
  pair : Symbols d
  /-- Whether this team is at the upper group. -/
  high : Bool
  /-- Absolute packet-bank base. -/
  base : ℕ
  /-- Packet-bank stride. -/
  stride : ℕ
  /-- Next incoming selector bit address at row entry. -/
  selector : ℕ
  /-- Next incoming crossing bit address at row entry. -/
  crossing : ℕ
  /-- Common selection encoded in the public routed prefix. -/
  select : Packet n d blocks → Selector n K h
  /-- Assigned physical demand words. -/
  demand : Packet n d blocks → Ends n → Fin (h*b) → Bool
  /-- Assigned physical supply words at the selected edge widths. -/
  supply : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool

namespace PacketRowData

variable {n d blocks b h K s w : ℕ} (D : PacketRowData n d blocks b h K s)

/-- The physical packet produced at a selected finite trial. -/
abbrev packet (t : Fin (packetTrials n d blocks)) (ok : packetTrialValid t) :=
  (packetRowEquiv D.axis D.pair ⟨t,ok⟩).val

/-- The two source cursors and complete memory after any scan prefix. -/
structure State (w : ℕ) where
  /-- Next selector word. -/
  sel : ℕ
  /-- Next crossing word. -/
  cross : ℕ
  /-- Memory including all preceding packet writes. -/
  mem : Memory w

/-- The body rectangle prepared for the actual owned side of this packet. -/
def body (p : Packet n d blocks) :=
  bodyPositions (D.select p) D.axis (ownerBit D.axis p.1.2 D.high) (D.demand p) (D.supply p)

/-- Routed cursors and destination of the native callback at a selected packet. -/
def cursor (p : Packet n d blocks) (z : State w) : Cursor :=
  ⟨z.sel,z.cross,RoutingISA.OwnedVertex.bankAt D.base D.stride p⟩

/-- The actual crossing length of this selected packet in the chosen cut. -/
def crossLength (p : Packet n d blocks) :=
  ∑ v : Vertex (n+1), payload (onEdge s) (D.select p).2 (v,D.axis)

/-- Scatter both the selector prefix and its selected data rectangle, in their native order. -/
def visit (p : Packet n d blocks) (z : State w) : State w :=
  let c := D.cursor p z
  let prefixImage := image (selectorPositions (D.select p)) c.dest z.mem
  ⟨z.sel+selectorWidth n K h,z.cross+D.crossLength p,image (D.body p) (c.dest+selectorWidth n K h) prefixImage⟩

/-- The exact chronological packet image up to local trial index `k`. -/
def before (m : Memory w) : ℕ → State w
  | 0 => ⟨D.selector,D.crossing,m⟩
  | k+1 =>
    let z := before m k
    match RoutingISA.OwnedVertex.packetAtNat D.axis D.pair k with
    | none => z
    | some p => D.visit p z

/-- A valid trial applies the physical update of its unique packet. -/
theorem before_visit (m : Memory w) (t : Fin (packetTrials n d blocks)) (ok : packetTrialValid t) :
    D.before m (t.val+1) = D.visit (D.packet t ok) (D.before m t.val) := by
  rw [before,(RoutingISA.OwnedVertex.selected_fields D.axis D.pair t ok).1]

/-- Invalid other-coordinate digits change neither routed cursor nor memory. -/
theorem before_skip (m : Memory w) (t : Fin (packetTrials n d blocks)) (no : ¬packetTrialValid t) :
    D.before m (t.val+1) = D.before m t.val := by
  rw [before]
  simp only [RoutingISA.OwnedVertex.packetAtNat,t.isLt,dite_true,Fin.eta,packetTrial,no,dite_false]

/-- Prepared source bits and separated destinations at every selected trial, as a condition on the
original row memory. -/
def PreparedRow (src : Set ℕ) (m : Memory w) : Prop :=
  ∀ (t : Fin (packetTrials n d blocks)) (ok : packetTrialValid t),
    let p := D.packet t ok
    Prepared src (selectorPositions (D.select p) ++ D.body p) (D.cursor p (D.before m t.val)) m

/-- Initial routed input stays resident through every finite prefix. -/
theorem before_source {src : Set ℕ} (m : Memory w) (ready : D.PreparedRow src m) (k : ℕ) :
    ∀ j ∈ src, (D.before m k).mem j = m j := by
  induction k with
  | zero => exact fun _ _ => rfl
  | succ k ih =>
    intro j hj
    by_cases hk : k < packetTrials n d blocks
    · let t : Fin (packetTrials n d blocks) := ⟨k,hk⟩
      by_cases ok : packetTrialValid t
      · let p := D.packet t ok
        rw [D.before_visit m t ok]
        obtain ⟨pre,suffix⟩ := (prepared_congr _ _ _ _ ih (ready t ok)).split
        rw [selectors_advance] at suffix
        exact (suffix.image_source hj).trans ((pre.image_source hj).trans (ih j hj))
      · rw [D.before_skip m t ok]
        exact ih j hj
    · rw [before]
      simpa only [RoutingISA.OwnedVertex.packetAtNat,hk,dite_false] using ih j hj

/-- Private choices at a candidate: the body word at a selected physical packet and the empty
sequence on an invalid trial. -/
def choices (t : Fin (packetTrials n d blocks)) :=
  if ok : packetTrialValid t then ((D.body (D.packet t ok)).map Position.digit).flatMap Digit.choices else []

end PacketRowData

end Cube.Scatter

end BorderVNP
end Computability
end OAI
