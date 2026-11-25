import OAI.Computability.BorderVNP.CubeScatterTransmissionAssigned
import OAI.Computability.BorderVNP.TransmissionAssignedProgram

/-! # Complete native route histories realizing prescribed cube row words

The starting state is the populated pre-scheduler RAM. Each team runs the
actual scheduler, relay checks, padding checks and transmission traversal. The
prescribed row payload selects exactly one chronological return on that
team. Both views of every strict pair read the assigned row word, and the
complete positive physical cost is retained. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {tab : TableLayout} {row : ℕ → TableRow} {pub : Fin (R+1) → Arg → Word w}
variable {before : Fin (R+1) → Memory w} {dst ib hb sb : Fin (R+1) → ℕ}
variable {guess : Fin (R+1) → ℕ → Bool}

/-- Genuine inputs to the route, including both descriptor writers' placement,
the actual physical processor words and the already made pin substitutions. -/
structure SharedRoutePrepared (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (L : WireLayout (R+1) r link) (D : Packing.Directory.Layout)
    (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (origin stride : ℕ) (tab : TableLayout)
    (row : ℕ → TableRow) (pub : Fin (R+1) → Arg → Word w) (before : Fin (R+1) → Memory w)
    (dst ib hb sb : Fin (R+1) → ℕ) (guess : Fin (R+1) → ℕ → Bool) : Prop where
  teams : R+1 = tab.teams
  widths : L.width = tableWidth tab row teams
  allocated : tab.Allocated w
  ordered : tab.Ordered
  rowFit : tab.RowsFit w row
  base : ∀ u, (pub u 0).val = tab.frame
  fields : ∀ u, tab.frameFields (readings (before u))
  records : ∀ u, tab.recordsMatch row (readings (before u))
  frame : ∀ u, (G.transferFrame u L.header (dst u)).At (readings (pub u)) (readings (before u))
  fit : ∀ u, (G.transferFrame u L.header (dst u)).Fits w (pub u 0).val
  capacity : ∀ u x y, L.header+legLoad allocated.teamCount (tab.widthMatrix row) x y+
    legLoad allocated.teamCount (tab.widthMatrix row) y x ≤ (G.transferFrame u L.header (dst u)).capacity
  physical : ∀ u, (G.processorFields u pin ext (ib u) (hb u) (sb u)).ContainsInput (before u)
  inputBefore : ∀ u, (G.processorFields u pin ext (ib u) (hb u) (sb u)).header.length ≤ tab.records
  written : ∀ u, WrittenPlacement tab row (before u) (pub u) D pp lp (fun c => (owner c).val)
    origin stride (G.pinLayout u (ib u) (hb u) (sb u))
  substituted : ∀ u, Pins.SubstitutionAt (G.pinLayout u (ib u) (hb u) (sb u)) (guess u) (before u)
  subBefore : ∀ u, ib u+(G.pinLayout u (ib u) (hb u) (sb u)).count ≤ tab.records

/-- Chronological subword of an assigned table containing exactly the
co-located slots selected by this team's traversal. -/
def assignedLocalSlots (rows : ℕ → Range w) (p : Arg → Word w) (m : Memory w) (bit : ℕ → ℕ → Bool) :
    LocalSlots rows p m :=
  let bs := tableChoiceBits rows (directoryFrame p m 0) bit (directoryFrame p m 13).val
  fun j => bs[j.val]'(j.isLt.trans_eq (tableChoiceBits_length ..).symm)

private theorem listOfDigits (xs : List Bool) (k : ℕ) (len : xs.length = k) :
    List.ofFn (fun j : Fin k => xs[j.val]'(j.isLt.trans_eq len.symm)) = xs := by
  subst k
  exact List.ofFn_getElem

/-- Enumerating the local slot function reproduces the event stream. -/
theorem assignedLocalSlots_word (rows : ℕ → Range w) (p : Arg → Word w) (m : Memory w) (bit : ℕ → ℕ → Bool) :
    List.ofFn (assignedLocalSlots rows p m bit) = tableChoiceBits rows (directoryFrame p m 0) bit (directoryFrame p m 13).val := by
  exact listOfDigits _ _ (tableChoiceBits_length ..)

variable {a q blocks K h : ℕ} {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}

/-- Run all teams on the prescribed shared payload and its physically assigned
exterior. Every local guess appears at its genuine chronological offset, each
positive return is unique for that tape, and the exact same raw word is read
back from the completed joint delivery. -/
theorem SharedRoutePrepared.realize
    (input : SharedRoutePrepared G pin ext L D pp lp owner origin stride tab row pub before dst ib hb sb guess)
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (regs : Fin (R+1) → Bank w)
    (emitted : ∀ u, g.Emitted (src u) (readings (before u))) (fitted : ∀ u, g.Fits w (src u))
    (records : tab.records = g.records) (count : tab.count = g.dataCount+g.groups.choose 2)
    (dataCount : (D.directory pp lp).length = g.dataCount) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (raw : Symbols q → List Bool) (lengths : ∀ p, (raw p).length = SharedRows.reserved blocks K h decl p)
    {fixed : Block (R+1)} {header : Fin L.header → Bool} {high : Fin (R+1) → Fin (R+1) → ℕ → Bool}
    (checks : Checks L.three L.width fixed header high
      (tab.recordPayload row (G.assignedRows guess D pp lp fun i => assignedShared g raw i.val)) (L.exteriorEquiv ext)) :
    ∃ (z : ∀ u, Returns route (pub u) (mac u) (regs u) (before u)) (H : Fin (R+1) → TeamHistory w)
      (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H (fun u => G.pinLayout u (ib u) (hb u) (sb u))),
      f.table = tab ∧ f.row = row ∧ SharedWriters f g src ∧ f.receivedRows g group = raw ∧
      ∀ u, (H u).history.val.2 = (z u).val.2 ∧
        (z u).val.1.flatMap TeamRAM.Event.choices = tableChoiceBits (H u).rows (H u).team (assignedShared g raw) (H u).count ∧
        (∀ alt : Returns route (pub u) (mac u) (regs u) (before u),
          alt.val.1.flatMap TeamRAM.Event.choices = (z u).val.1.flatMap TeamRAM.Event.choices → alt = z u) ∧
        traceCost (z u).val.1 ≤ routeSetupBudget tab row (G.transferFrame u L.header (dst u)) +
          256*(1+tab.count+∑ i ∈ Finset.range tab.count, ((H u).rows i).incident (H u).team) ∧
        ∀ e ∈ (z u).val.1, e.sign = .plus := by
  choose m sched _image E effects using fun u => assigned_route_from_input u (ib u) (hb u) (sb u) (dst u)
    (pub u) (mac u) (regs u) (before u) tab row input.teams input.widths input.allocated input.ordered input.rowFit
    (input.base u) (input.fields u) (input.records u) (input.frame u) (input.fit u) (input.capacity u)
    (input.physical u) (input.inputBefore u) (input.written u) guess (fun i => assignedShared g raw i.val)
    (input.substituted u) (input.subBefore u) checks
  let slots u := assignedLocalSlots (tableRange tab (m u)) (pub u) (m u) (assignedShared g raw)
  let z u := E u (slots u)
  obtain ⟨H,f,ft,fr,fb,real⟩ := exists_delivery_of_routes tab row pub mac regs before _ z input.allocated input.ordered
    input.rowFit input.teams input.widths input.base input.fields input.records dst ib hb sb input.frame input.fit
    input.capacity input.physical input.inputBefore input.written
  let writer : SharedWriters f g src :=
    ⟨fun u => fb ▸ emitted u,fitted,ft ▸ records,ft ▸ count,room⟩
  have initial (u : Fin (R+1)) : (H u).initial = m u := by
    obtain ⟨log,t',run⟩ := (real u).2.2.2.2.2.2.1
    obtain ⟨log',t'',run'⟩ := sched u
    exact (run.unique_of_deterministic (by decide) run').2.2
  have rows (u : Fin (R+1)) : (H u).rows = tableRange tab (m u) := (real u).2.2.2.1.trans (congrArg _ (initial u))
  have p (u : Fin (R+1)) := (real u).2.2.2.2.1
  have word (u : Fin (R+1)) : (z u).val.1.flatMap TeamRAM.Event.choices =
      tableChoiceBits (H u).rows (H u).team (assignedShared g raw) (H u).count := by
    rw [TeamHistory.team,TeamHistory.count,rows,p,initial]
    exact (effects u (slots u)).1.trans (assignedLocalSlots_word ..)
  have checked : Checks L.three L.width fixed header high
      (f.table.recordPayload f.row (G.assignedRows guess D pp lp fun i => assignedShared g raw i.val)) (L.exteriorEquiv ext) := by
    let ok (table : TableLayout) (rs : ℕ → TableRow) := Checks L.three L.width fixed header high
      (table.recordPayload rs (G.assignedRows guess D pp lp fun i => assignedShared g raw i.val)) (L.exteriorEquiv ext)
    change ok f.table f.row
    rw [ft,fr]
    exact checks
  have recovered := writer.received_assigned frame raw lengths dataCount guess checked
    (fun u => (real u).2.1.trans (word u))
  refine ⟨z,H,f,ft,fr,writer,recovered,fun u => ⟨(real u).1,word u,?_,?_,(effects u _).2.2.2⟩⟩
  · intro alt tape
    obtain ⟨v,rfl⟩ := (E u).surjective alt
    exact congrArg (E u) (List.ofFn_injective ((effects u v).1.symm.trans (tape.trans (effects u (slots u)).1)))
  · rw [TeamHistory.team,rows,p,initial]
    exact (effects u (slots u)).2.2.1

end TeamContraction

end BorderVNP
end Computability
end OAI
