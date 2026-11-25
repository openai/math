import OAI.Hierarchy.DescentOriginalArgumentPointer
import OAI.Hierarchy.DescentOccurrenceAllowance
import OAI.Hierarchy.DescentOperandWidth

namespace OAI
/-! Bounds on the four fields of a reached reset operand before its next encoding. -/
namespace Hierarchy.DescentSixParty.Reached
open DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentLocalPrivateNames
open DescentSharedCableNames DescentOperandStateBanks DescentCompiler DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false

private theorem privateAddress_room {tag port : Type} (r : Recipe tag port) (address : Slot r→ℕ)
    (word : r.UsedWord) {limit : ℕ} (low : ∀j,address j<limit) : privateAddress r address word<limit:=by
  obtain ⟨used,found⟩:=hit r word
  have existsAddress : ∃n,∃j : Slot r,address j=n ∧ read r j=some word:=⟨_,used,rfl,found⟩
  obtain ⟨j,h,_⟩:=Nat.find_spec existsAddress
  change Nat.find existsAddress < limit
  exact h ▸ low j

private theorem issued_cable_header {w peer serial slice : ℕ} (tag : 1<2^w)
    (peerFits : peer<2^w) (serialFits : serial<2^w) (sliceFits : slice<2^w) (f : Fin 4) :
    (Pointer.cable peer serial slice).header f<2^w:=by
  fin_cases f <;> simp [Pointer.header,tag,peerFits,serialFits,sliceFits]

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist p R : ℕ}
  (cap : Reached W G q ε S k age grain degree wire hist) (hp : 0<p)
  (v : W.graph.Site) (edge : Incident W.graph v) (chunk : ℕ) (fits : (chunk+1)*p≤W.graph.width edge.val)

theorem firstCable_header_bounds {w : ℕ} (tag : 1<2^w)
    (rankRoom : cap.placement.degree≤2^w) (wireRoom : cap.placement.cap≤2^w)
    (chunkRoom : chunk<2^w) (f : Fin 4) : (firstCable cap hp v edge chunk fits).header f<2^w:=by
  unfold firstCable
  exact issued_cable_header tag ((Fin.isLt _).trans_le rankRoom) ((Fin.isLt _).trans_le wireRoom) chunkRoom f

/-- Each word of a real cable fits in the public slice counter of the attained calendar. -/
theorem firstCable_dated_room {tail drift upper : ℕ} (ageFits : age≤S.length)
    (positive : 0<S.height) (grainAt : grain=S.grainAt G.b p age) (base : G.b≤2^S.capGain)
    (degreeFits : degree≤DescentOperandWidth.bound G S drift upper) (f : Fin 4) :
    (firstCable cap hp v edge chunk fits).header f<2^(DescentOperandWidth.s G S k tail drift upper):=by
  let w:=DescentOperandWidth.s G S k tail drift upper
  have limbs : W.graph.width edge.val≤p*DescentOperandWidth.slices S:=
    cap.placement.cable_room S edge.val positive ageFits (cap.grain.trans grainAt) base cap.valid.capacity
  have n : chunk+1≤DescentOperandWidth.slices S:=by
    exact Nat.le_of_mul_le_mul_right ((fits.trans limbs).trans_eq (Nat.mul_comm ..)) hp
  have capRoom : cap.placement.cap≤DescentOperandWidth.publicCap S:=
    cap.valid.capacity.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left _ ageFits) _))
  have rawFits : cap.placement.cap≤DescentOperandWidth.raw S:=by
    unfold DescentOperandWidth.raw
    omega
  have rawRoom : DescentOperandWidth.raw S≤DescentOperandWidth.bound G S drift upper:=
    (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  refine firstCable_header_bounds cap hp v edge chunk fits ?_ ?_ ?_ ?_ f
  · exact (by decide : 1<2^2).trans_le (Nat.pow_le_pow_right (by decide) (DescentOperandWidth.wide G S k tail drift upper))
  · rw [cap.branch]
    exact (DescentOperandWidth.numeric G S degreeFits).le
  · exact (DescentOperandWidth.numeric G S (rawFits.trans rawRoom)).le
  · exact DescentOperandWidth.rangeField G S ((Nat.le_succ _).trans n)

variable (B : BitDescription W) (number : Local B) (shape : WorldShape p R B) (pin : P→ℕ)
local notation "rec_" => (shape.sites v).recipe hp

/-- On the original cable branch, a real live port supplies the successor's
peer, serial and subword. This applies even before determining which port it was. -/
theorem argument_cable_header_room (a : ℕ) (node : (B.recipe v).Node) (index : ℕ)
    {tail drift upper : ℕ} (ageFits : age≤S.length) (positive : 0<S.height)
    (grainAt : grain=S.grainAt G.b p age) (base : G.b≤2^S.capGain) (degreeFits : degree≤DescentOperandWidth.bound G S drift upper)
    (peer serial chunk : ℕ) (isCable : argumentPointer cap B number shape hp pin a ⟨v,node⟩ index=
      Pointer.cable peer serial chunk) (f : Fin 4) :
    (argumentPointer cap B number shape hp pin a ⟨v,node⟩ index).header f<
      2^(DescentOperandWidth.s G S k tail drift upper):=by
  by_cases active : index<(rec_).arity node
  · let j : Fin ((rec_).arity node):=⟨index,active⟩
    cases word : (rec_).activePort node j with
    | inr privateWord=>
      simp only [argumentPointer,dite_eq_left active,show (⟨index,active⟩:Fin ((rec_).arity node))=j from rfl,word]
        at isCable
      cases isCable
    | inl ref=>
      obtain ⟨edge|socket,part,legal⟩:=ref
      · simpa only [argumentPointer,dite_eq_left active,show (⟨index,active⟩:Fin ((rec_).arity node))=j from rfl,word]
          using firstCable_dated_room (tail:=tail) (drift:=drift) cap hp v edge part legal ageFits positive grainAt
            base degreeFits f
      · simp only [argumentPointer,dite_eq_left active,show (⟨index,active⟩:Fin ((rec_).arity node))=j from rfl,word]
          at isCable
        cases isCable
  · simp only [argumentPointer,dite_eq_right active] at isCable
    cases isCable

/-- The finite rectangle bounds the renamed private word. Each exterior pin
uses its previous four header words and each cable uses its actual reached endpoint. -/
theorem argument_reset_header_room (a : ℕ) (node : (B.recipe v).Node) (j : Fin ((rec_).arity node))
    {w : ℕ} (live : 0<2^w)
    (slots : ∀u,(rec_).arity u≤a) (rect : Fintype.card (B.recipe v).Node*a≤2^w)
    (cables : ∀(e : Incident W.graph v) (chunk : ℕ) (fit : (chunk+1)*p≤W.graph.width e.val) (f : Fin 4),
      (firstCable cap hp v e chunk fit).header f<2^w)
    (pins : ∀(port : Attached W.graph v) (chunk : ℕ) (fit : (chunk+1)*p≤bits port.val),
      (rec_).operand node j=.inl ⟨.inr port,chunk,fit⟩ →
      ∀f : Fin 4,(Pointer.pin (pin port.val) chunk).header f<2^w) (f : Fin 4) :
    (argumentPointer cap B number shape hp pin a ⟨v,node⟩ j.val).header f<2^w:=by
  cases source : (rec_).activePort node j with
  | inr z =>
    have size : privateAddress rec_ (fun t=>(number v t.1).val*a+t.2.val) z<2^w:=by
      apply privateAddress_room
      intro t
      calc
        _ < (number v t.1).val*a+a := Nat.add_lt_add_left (t.2.isLt.trans_le (slots t.1)) _
        _ = ((number v t.1).val+1)*a := (Nat.succ_mul ..).symm
        _ ≤ _ := (Nat.mul_le_mul_right a (number v t.1).isLt).trans rect
    simp only [argumentPointer,dite_eq_left j.isLt,Fin.eta,source]
    fin_cases f <;> simp [Pointer.header,live,size]
  | inl ref =>
    obtain ⟨e|port,chunk,fit⟩:=ref
    · simpa only [argumentPointer,dite_eq_left j.isLt,Fin.eta,source] using cables e chunk fit f
    · have assigned : (rec_).operand node j=.inl ⟨.inr port,chunk,fit⟩ := by
        simpa only [source,Sum.map_inl,id_eq] using ((rec_).activePort_read node j).symm
      simpa only [argumentPointer,dite_eq_left j.isLt,Fin.eta,source] using pins port chunk fit assigned f

end
end Hierarchy.DescentSixParty.Reached

end OAI
