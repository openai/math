import OAI.Computability.BorderVNP.TransmissionRouteFactory
import OAI.Computability.BorderVNP.TransmissionReceivedPrivate

/-! # Assembling the placed delivery from actual complete four-stage native routes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}

/-- Actual full native route returns on every team reconstruct a single delivery
context for all private and live lanes. The complete final register/memory pair
and chronological choices are those of the given physical runs. The written
layout is constructed from the two descriptor writers by `WrittenPlacement.of_writers`. -/
theorem exists_delivery_of_routes (tab : TableLayout) (row : ℕ → TableRow)
    (pub : Fin (R+1) → Arg → Word w) (mac : Fin (R+1) → TeamOpcode.Macros w 8)
    (s : Fin (R+1) → Bank w) (before : Fin (R+1) → Memory w) (pins : Fin (R+1) → Pins.Layout)
    (z : ∀ u, Returns route (pub u) (mac u) (s u) (before u))
    (al : tab.Allocated w) (ordered : tab.Ordered) (rowsFit : tab.RowsFit w row)
    (teams : R+1 = tab.teams) (widths : wire.width = tableWidth tab row teams)
    (base : ∀ u, (pub u 0).val = tab.frame)
    (fields : ∀ u, tab.frameFields (readings (before u))) (records : ∀ u, tab.recordsMatch row (readings (before u)))
    (dst ib hb sb : Fin (R+1) → ℕ)
    (frame : ∀ u, (G.transferFrame u wire.header (dst u)).At (readings (pub u)) (readings (before u)))
    (fit : ∀ u, (G.transferFrame u wire.header (dst u)).Fits w (pub u 0).val)
    (capacity : ∀ u x y, wire.header+legLoad al.teamCount (tab.widthMatrix row) x y+
      legLoad al.teamCount (tab.widthMatrix row) y x ≤ (G.transferFrame u wire.header (dst u)).capacity)
    (physical : ∀ u, (G.processorFields u pin ext (ib u) (hb u) (sb u)).ContainsInput (before u))
    (inputBefore : ∀ u, (G.processorFields u pin ext (ib u) (hb u) (sb u)).header.length ≤ tab.records)
    (written : ∀ u, WrittenPlacement tab row (before u) (pub u) D pp lp (fun c => (owner c).val) origin stride (pins u)) :
    ∃ (H : Fin (R+1) → TeamHistory w) (f : ReturnedDelivery G pin ext wire D pp lp owner origin stride H pins),
      f.table = tab ∧ f.row = row ∧ f.before = (fun u => readings (before u)) ∧
      ∀ u, (H u).history.val.2 = (z u).val.2 ∧
        (H u).history.val.1.flatMap TeamRAM.Event.choices = (z u).val.1.flatMap TeamRAM.Event.choices ∧
        tab.Image row (readings (before u)) (readings (H u).initial) ∧ (H u).rows = tableRange tab (H u).initial ∧
        (H u).pub = pub u ∧ (H u).macros = mac u ∧
        (∃ log t, Runs (pub u) (mac u) scheduleTable (s u) (before u) log t (H u).initial) ∧
        routingChecks tab row (G.transferFrame u wire.header (dst u)) (pub u) (fit u) teams (H u).initial := by
  choose H hpub hmac hr hc image checked final choices log bank installed using fun u =>
    route_history_of_return tab row (pub u) (mac u) (s u) (before u) al ordered rowsFit (base u)
      (fields u) (records u) _ (frame u) (fit u) teams (capacity u) (written u).route (z u)
  have transferred u := (written u).placed (H u) (hr u) (hc u) (image u)
  have B (u : Fin (R+1)) : HistoryBank G pin ext wire.width wire.header u (H u) (tab.readExtent (pins u)) :=
    HistoryBank.ofScheduled u (ib u) (hb u) (sb u) (dst u) (tab.readExtent (pins u)) teams widths (image u) al ordered
      ((hpub u).symm ▸ base u) (fields u) ((hpub u).symm ▸ frame u) ((hpub u).symm ▸ fit u)
      (capacity u) (physical u) (inputBefore u) (tab.readExtent_bounds _).1
  have relays u v (p : Hop wire.three wire.width u v) := (B v).checked_of_route teams widths
    ((hpub v).symm ▸ fit v) (by simpa only [hpub v] using checked v) u p
  refine ⟨H,⟨(written 0).word,tab,B,transferred,fun v => (B v).initial,relays,row,fun u => readings (before u),
    teams,widths,al,rowsFit,records,image,hr,hc,(written 0).count,(written 0).positive,
    fun u => (written u).dimensions,fun u => (written u).sourceRoom⟩,rfl,rfl,rfl,
    fun u => ⟨final u,choices u,image u,hr u,hpub u,hmac u,⟨log u,bank u,installed u⟩,checked u⟩⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
