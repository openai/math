import OAI.Computability.BorderVNP.CubeScatterTransmissionAssigned
import OAI.Computability.BorderVNP.TransmissionReverseSend

/-! # The prescribed value of every shared or data hop on a returning route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter
open private hop_relay from OAI.Computability.BorderVNP.TransmissionAcross
open private index_covered from OAI.Computability.BorderVNP.TransmissionSharedLastWrite
open private receivedWord_at from OAI.Computability.BorderVNP.CubeScatterTransmissionAssigned

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {a q blocks K h : ℕ}
variable {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

private theorem hop_ext {N : ℕ} {three : 2 < N} {width : Fin N → Fin N → ℕ}
    {u v : Fin N} {p p' : Hop three width u v} (peer : p.1 = p'.1) (ordinal : p.2.val = p'.2.val) :
    p = p' := by
  obtain ⟨z,k,hk⟩ := p
  obtain ⟨z',k',hk'⟩ := p'
  change z = z' at peer
  change k = k' at ordinal
  subst z'; subst k'; rfl

/-- The outgoing hop of any strict row contains the digit of that same row's
reconstructed ordered bank. No agreement with a preassigned expansion is assumed. -/
theorem SharedWriters.remote_shared_hop (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group) (sym : Symbols q)
    {u v : Fin (R+1)} (p : Hop L.three L.width u v) (j : ℕ) (inside : j < (f.row (sharedIndex g sym)).width)
    (first : (f.row (sharedIndex g sym)).first = u.val) (second : (f.row (sharedIndex g sym)).second = p.1.val)
    (ord : p.2.val = f.table.ordinal f.row (sharedIndex g sym)+j) :
    (L.exteriorEquiv ext).hop u v p = assignedShared g (f.receivedRows g group) (sharedIndex g sym) j := by
  obtain ⟨z,k,hk⟩ := p
  let hop : Hop L.three L.width u v := ⟨z,⟨k,hk⟩⟩
  obtain ⟨diff,hv⟩ := hop_relay hop
  change u ≠ z at diff
  change Routing.relay L.three diff k = v at hv
  clear hop
  subst v
  change k = f.table.ordinal f.row (sharedIndex g sym)+j at ord
  subst k
  let y := sym.val.2
  have bg : y.val < g.groups := frame.groups ▸ y.isLt
  obtain ⟨p',peer,ordinal,digit⟩ := writer.remote_digit u z diff sym.property bg first second inside
  have he : p' = ⟨z,⟨f.table.ordinal f.row (sharedIndex g sym)+j,hk⟩⟩ := hop_ext peer ordinal
  rw [he] at digit
  have ueq : group sym.val.1 = u := Fin.ext ((writer.declaredRows frame sym).1.symm.trans first)
  have len : j < (f.receivedRows g group sym).length := by
    simpa only [ReturnedDelivery.receivedRows,receivedWord_length,sharedIndex] using inside
  rw [assignedShared_at _ _ _ _ len]
  have read := receivedWord_at (H (group sym.val.1)).history.val.2.2 (g.view sym.val.1 y)
    (f.row (sharedIndex g sym)).width j len
  exact digit.symm.trans ((congrArg (fun t => decide (((H t).history.val.2.2 (g.view sym.val.1 y+j)).val=1)) ueq.symm).trans read.symm)

/-- The same reconstructed digit occurs on either leg of an arbitrary shared
table bit, including every position of the compact triangular suffix. -/
theorem SharedWriters.shared_pair_value (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group) {u v : Fin (R+1)} (p : Hop L.three L.width u v)
    (i : Fin f.table.count) (shared : g.dataCount ≤ i.val) (j : ℕ) (inside : j < (f.row i).width)
    (ends : (f.row i).first = u.val ∧ (f.row i).second = p.1.val ∨
      (f.row i).first = p.1.val ∧ (f.row i).second = u.val)
    (ord : p.2.val = f.table.ordinal f.row i+j) :
    (L.exteriorEquiv ext).hop u v p = assignedShared g (f.receivedRows g group) i j := by
  obtain ⟨y,hy,x,hxy,index⟩ := index_covered g shared (writer.count ▸ i.isLt)
  let sym : Symbols q := ⟨(⟨x,frame.groups ▸ hxy.trans hy⟩,⟨y,frame.groups ▸ hy⟩),hxy⟩
  have idx : i.val = sharedIndex g sym := index
  rw [idx] at inside ends ord ⊢
  rcases ends with ⟨first,second⟩ | ⟨first,second⟩
  · exact writer.remote_shared_hop frame sym p j inside first second ord
  · exact (((f.relay v).relay_hop_iff f.word p).mp (f.checked u v p)).trans
      (writer.remote_shared_hop frame sym (otherHop L.three L.width p) j inside first second ord)

variable {ib hb sb : Fin (R+1) → ℕ}
local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)

/-- For every actually scheduled nonlocal bit, the returned exterior gives
exactly the recovered shared bit or the literal/substitution forced by its data
record. The value is the one used by the forward transmission constructor. -/
theorem SharedWriters.returned_record_value {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H PL}
    (writer : SharedWriters f g src) (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (dataCount : (D.directory pp lp).length = g.dataCount) (guess : Fin (R+1) → ℕ → Bool)
    (sub : ∀ u, Pins.SubstitutionAt (PL u) (guess u) (H u).initial)
    {u v : Fin (R+1)} (p : Hop L.three L.width u v) (i : Fin f.table.count) (j : ℕ) (inside : j < (f.row i).width)
    (ends : (f.row i).first = u.val ∧ (f.row i).second = p.1.val ∨
      (f.row i).first = p.1.val ∧ (f.row i).second = u.val)
    (ord : p.2.val = f.table.ordinal f.row i+j) :
    (L.exteriorEquiv ext).hop u v p =
      G.assignedRows guess D pp lp (fun k => assignedShared g (f.receivedRows g group) k.val) i j := by
  by_cases data : i.val < (D.directory pp lp).length
  · let k : Fin (D.directory pp lp).length := ⟨i.val,data⟩
    obtain ⟨_,_,_,width,_⟩ := tableRange_fields (f.image u) f.allocated (f.records u) i.isLt
    rw [← f.ranges u] at width
    have fit : j < (D.directory pp lp)[k.val].width :=
      inside.trans_eq (width.symm.trans ((f.placed u).columns.width k))
    rw [Wiring.assignedRows,dite_eq_left data]
    exact f.data_pair_value guess sub p k ⟨j,fit⟩ ends ord
  · rw [Wiring.assignedRows,dite_eq_right data]
    exact writer.shared_pair_value frame p i (dataCount ▸ Nat.le_of_not_gt data) j inside ends ord

end TeamContraction

end BorderVNP
end Computability
end OAI
