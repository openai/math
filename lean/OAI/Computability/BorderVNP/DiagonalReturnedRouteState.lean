import OAI.Computability.BorderVNP.RoutingISASignedPrepRouteFiber

/-! # The returned route's named records, frames and destination rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube Physical Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {tab : TableLayout} {row : ℕ → TableRow} {pub : Fin (R+1) → Arg → Word w}
    {before : Fin (R+1) → Memory w} {dst ib hb sb : Fin (R+1) → ℕ}
    {guess : Fin (R+1) → ℕ → Bool}
    (input : SharedRoutePrepared G pin ext L D pp lp owner origin stride tab row pub before dst ib hb sb guess)
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (regs : Fin (R+1) → Bank w)
    (z : ∀ u, Returns route (pub u) (mac u) (regs u) (before u))
    {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}

include input in
/-- Keep the RAM, opcode library and register files of the very same
returning route when installing its delivered physical words. The row
decoder is evaluated on its actual destination memory. -/
theorem SharedRoutePrepared.ownedDelivery
    (emitted : ∀ u, g.Emitted (src u) (readings (before u))) (fitted : ∀ u, g.Fits w (src u))
    (records : tab.records=g.records) (count : tab.count=g.dataCount+g.groups.choose 2)
    (room : g.banks+g.stride*g.groups^2≤2^w) :
    ∃ (H : Fin (R+1) → TeamHistory w) (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H
        (fun u => G.pinLayout u (ib u) (hb u) (sb u))),
      f.table=tab ∧ f.row=row ∧ f.before=(fun u => readings (before u)) ∧ SharedWriters f g src ∧
      (∀ u, (H u).pub=pub u ∧ (H u).macros=mac u ∧ (H u).history.val.2=(z u).val.2) ∧
      (∀ u, Pins.SubstitutionAt (G.pinLayout u (ib u) (hb u) (sb u)) (guess u) (H u).initial) ∧
      ∀ {a : ℕ} (group : Fin a → Fin (R+1)), f.receivedRows g group =
        readRouteRows row g group (fun u => (z u).val.2.2) := by
  obtain ⟨H,f,ft,fr,fb,real⟩ := exists_delivery_of_routes tab row pub mac regs before _ z
    input.allocated input.ordered input.rowFit input.teams input.widths input.base input.fields input.records
    dst ib hb sb input.frame input.fit input.capacity input.physical input.inputBefore input.written
  have writer : SharedWriters f g src :=
    ⟨fun u => fb ▸ emitted u,fitted,ft ▸ records,ft ▸ count,room⟩
  have pinned (u : Fin (R+1)) :
      Pins.SubstitutionAt (G.pinLayout u (ib u) (hb u) (sb u)) (guess u) (H u).initial := by
    intro j hj
    change j < (G.pinLayout u (ib u) (hb u) (sb u)).count at hj
    have bound := input.subBefore u
    have same := (real u).2.2.1.before_records input.ordered (by omega : ib u+j < tab.records)
    exact (Fin.ext same).trans (input.substituted u j hj)
  refine ⟨H,f,ft,fr,fb,writer,fun u => ⟨(real u).2.2.2.2.1,(real u).2.2.2.2.2.1,(real u).1⟩,pinned,?_⟩
  intro a group
  funext i
  simp only [ReturnedDelivery.receivedRows,readRouteRows,sharedIndex,fr,
    show (H (group i.val.1)).history.val.2.2=(z (group i.val.1)).val.2.2 from congrArg Prod.snd (real _).1]

end TeamContraction

end BorderVNP
end Computability
end OAI
