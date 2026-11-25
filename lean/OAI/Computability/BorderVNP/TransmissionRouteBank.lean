import OAI.Computability.BorderVNP.TransmissionPlacedRoute
import OAI.Computability.BorderVNP.TransmissionReceivedFields

/-! # The initialized transfer bank and relay checks supplied by a complete route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}

/-- A true scheduled processor bank, available before any transmission return exists. -/
def TransferBank.ofScheduled {tab : TableLayout} {row : ℕ → TableRow} {before mt : Memory w} (pub : Arg → Word w)
    (u : Fin (R+1)) (ib hb sb dst : ℕ) (teams : R+1 = tab.teams)
    (widths : wire.width = tableWidth tab row teams) (image : tab.Image row (readings before) (readings mt))
    (al : tab.Allocated w) (ordered : tab.Ordered) (base : (pub 0).val = tab.frame)
    (fields : tab.frameFields (readings before))
    (frame : (G.transferFrame u wire.header dst).At (readings pub) (readings before))
    (fit : (G.transferFrame u wire.header dst).Fits w (pub 0).val)
    (capacity : ∀ x y, wire.header + legLoad al.teamCount (tab.widthMatrix row) x y +
      legLoad al.teamCount (tab.widthMatrix row) y x ≤ (G.transferFrame u wire.header dst).capacity)
    (input : (G.processorFields u pin ext ib hb sb).ContainsInput before)
    (inputBefore : (G.processorFields u pin ext ib hb sb).header.length ≤ tab.records)
    : TransferBank G pin ext wire.width w wire.header u := by
  let physical : (G.processorFields u pin ext ib hb sb).ContainsInput mt := fun i hi =>
    (Fin.ext (image.before_records ordered (hi.trans_le inputBefore))).trans (input i hi)
  have schedule := Schedule.of_table image al pub base fields _ (image.broadcast_of_ordered ordered base frame)
    fit teams capacity
  exact ⟨pub,mt,ib,hb,sb,dst,physical,by rw [widths]; exact schedule⟩

/-- The scheduling pass and successful read-only checks supply the actual physical
entry bank of a native transfer. Its frame, table and original processor-tape words
survive below the cell banks. -/
def HistoryBank.ofScheduled {tab : TableLayout} {row : ℕ → TableRow} {before : Memory w} {H : TeamHistory w}
    (u : Fin (R+1)) (ib hb sb dst origin : ℕ) (teams : R+1 = tab.teams)
    (widths : wire.width = tableWidth tab row teams) (image : tab.Image row (readings before) (readings H.initial))
    (al : tab.Allocated w) (ordered : tab.Ordered) (base : (H.pub 0).val = tab.frame)
    (fields : tab.frameFields (readings before))
    (frame : (G.transferFrame u wire.header dst).At (readings H.pub) (readings before))
    (fit : (G.transferFrame u wire.header dst).Fits w (H.pub 0).val)
    (capacity : ∀ x y, wire.header + legLoad al.teamCount (tab.widthMatrix row) x y +
      legLoad al.teamCount (tab.widthMatrix row) y x ≤ (G.transferFrame u wire.header dst).capacity)
    (input : (G.processorFields u pin ext ib hb sb).ContainsInput before)
    (inputBefore : (G.processorFields u pin ext ib hb sb).header.length ≤ tab.records)
    (after : tab.ordinals+tab.count ≤ origin) : HistoryBank G pin ext wire.width wire.header u H origin := by
  let A := TransferBank.ofScheduled H.pub u ib hb sb dst teams widths image al ordered base fields frame fit
    capacity input inputBefore
  have protectedField (i : ℕ) (hi : i ≤ 25) :
      frameField (readings H.pub) (readings H.initial) i = readings before (tab.frame+i) := by
    unfold frameField readings; rw [base]; exact image.before_records ordered (by have := ordered.frame; omega)
  obtain ⟨fr,re,wd,ofst,use⟩ := ordered
  refine ⟨A,rfl,rfl,by change (G.processorFields u pin ext ib hb sb).header.length ≤ origin; omega,?_⟩
  change scheduleCeiling (readings H.pub) (readings H.initial) (R+1) ≤ origin
  rw [scheduleCeiling,protectedField 17 (by decide),protectedField 18 (by decide),fields.2.2.2.2.1,fields.2.2.2.2.2.1,teams]
  change max ((H.pub 0).val+26) (max (tab.offsets+tab.teams^3) (tab.used+tab.teams^2)) ≤ origin
  omega

/-- The complete route's sound relay predicate at its entry memory gives every
physical hop comparison used by the receipt theorem. -/
theorem HistoryBank.checked_of_route {tab : TableLayout} {row : ℕ → TableRow} {H : TeamHistory w} {origin dst : ℕ}
    {v : Fin (R+1)} (B : HistoryBank G pin ext wire.width wire.header v H origin)
    (teams : R+1 = tab.teams) (widths : wire.width = tableWidth tab row teams)
    (fit : (G.transferFrame v wire.header dst).Fits w (H.pub 0).val)
    (checked : routingChecks tab row (G.transferFrame v wire.header dst) H.pub fit teams H.initial)
    (u : Fin (R+1)) (p : Hop wire.three wire.width u v) :
    RelayWordAgrees (readings B.initial.pub) (readings B.initial.mem) u v p.1 (p.2.val/(R+1-2)) := by
  rw [B.args,B.memory]
  obtain ⟨f,count,k,records,ws,off,used,ord⟩ := tab
  change R+1 = count at teams
  subst count
  let l : TableLayout := ⟨f,R+1,k,records,ws,off,used,ord⟩
  have hw : wire.width = l.widthMatrix row := widths
  have check : RelayChecks (R+1) (fun x y => l.partnerLength row x v y) (readings H.pub) (readings H.initial) v := checked.2
  have all := (relayChecks_iff_hops l row wire.three v (readings H.pub) (readings H.initial)).mp check
  rw [← hw] at all
  exact all u p

end TeamContraction

namespace RoutingISA.Pins

open VPVNP.BurstRAM Transmission
open Packing.Directory.ISA (putWords_outside)

/-- The actual native data compiler, shared pair appender, and public scheduler all
preserve the prepared substitution array between the count header and record region.
This covers both an index team's guesses and every clamped zero. -/
theorem SubstitutionAt.through_writers {w : ℕ} {P : Layout} {guess : ℕ → Bool} {m mt : Memory w}
    (initial : SubstitutionAt P guess m) (emit : DataWriter.Layout) (pub : Arg → Word w)
    {g : Cube.SharedRows.Layout} {before : ℕ → ℕ}
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) before)
    (frame : g.frame = (pub 0).val) (records : g.records = emit.output)
    {tab : TableLayout} {row : ℕ → TableRow} (image : tab.Image row before (readings mt))
    (ordered : tab.Ordered) (out : tab.records = emit.output)
    (header : (pub 0).val+13 < P.ibase) (endAt : P.ibase+P.count ≤ emit.output) : SubstitutionAt P guess mt := by
  intro x hx
  apply Fin.ext
  have lo : P.ibase+x < emit.output := by omega
  have keep := image.before_records ordered (out ▸ lo)
  have other := shared.outside (P.ibase+x) (by rw [frame]; omega)
    (Or.inl (by unfold Cube.SharedRows.Layout.address; rw [records]; omega))
  have wrote : DataWriter.publish emit pub m (P.ibase+x) = m (P.ibase+x) := by
    rw [DataWriter.publish,Function.update_of_ne (by omega : P.ibase+x ≠ (pub 0).val+13),
      putWords_outside _ _ _ _ (Or.inl lo)]
  exact keep.trans (other.trans (congrArg Fin.val (wrote.trans (initial x hx))))

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
