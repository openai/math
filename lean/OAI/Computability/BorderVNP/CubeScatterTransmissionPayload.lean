import OAI.Computability.BorderVNP.CubeScatterTransmissionViews
import OAI.Computability.BorderVNP.CubeScatterCommonDecoder
import OAI.Computability.BorderVNP.CubePhysicalGreedyTally

/-! # Decoding the actual transmitted words of the cube declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
local notation "Delivery" => ReturnedDelivery G pin ext L D pp lp owner origin stride H pins
variable {a q blocks K h b s : ℕ}

/-- The physical declaration and owner words in the actual shared writer's
input memory. One team suffices because the common scheduler agrees on rows. -/
structure SymbolFrame (g : SharedRows.Layout) (mem : ℕ → ℕ) (blocks K h : ℕ)
    (decl : LengthDeclaration a q) (group : Fin q → Fin (R+1)) : Prop
    extends SharedRows.DeclarationFields g mem blocks K h decl where
  /-- The owner word for every group is the one read by the emitter. -/
  owners : ∀ x : Fin q, mem (g.owners+x.val) = (group x).val

/-- Before validating a selector, the owners are already the exact greedy
assignment on the advertised weights read by the native group schedule. -/
theorem SymbolFrame.of_schedule {g : SharedRows.Layout} {l : GroupWeights.Layout} {teams : TeamNative.Layout}
    {before mem : ℕ → ℕ} {decl : LengthDeclaration a l.groups}
    (result : GroupWeights.ScheduleResult l teams before mem)
    (declared : SharedRows.DeclarationFields g mem blocks K h decl) (aligned : g.owners = teams.owners) :
    SymbolFrame g mem blocks K h decl (fun x => TeamNative.owner teams.r (l.weight before) x.val) :=
  ⟨declared,fun x => aligned ▸ result.owners x.val x.isLt⟩

/-- The actual native group-weight and least-load schedule supplies the owners
of the specific passing packet selector tuple. -/
theorem SymbolFrame.of_greedy {g : SharedRows.Layout} {l : GroupWeights.Layout} {teams : TeamNative.Layout}
    {before mem : ℕ → ℕ} {decl : LengthDeclaration a l.groups} {A : Type*} [Fintype A]
    (result : GroupWeights.ScheduleResult l teams before mem)
    (select : Packet a l.groups blocks → Selector a K h) (pass : passesLengths b s select decl)
    (label : Fin l.cells → Label (a+1) l.groups) (recv : A → Fin l.cells) (dataWidth : A → ℕ)
    (image : GroupWeights.PhysicalImage l before blocks b K h decl label recv dataWidth)
    (declared : SharedRows.DeclarationFields g mem blocks K h decl) (aligned : g.owners = teams.owners) :
    SymbolFrame g mem blocks K h decl (greedyOwner teams.r b s label recv dataWidth select) :=
  ⟨declared, fun x => aligned ▸ greedyOwner_stored result select pass label recv dataWidth image x⟩

/-- One raw word per strict unordered pair, read from its lower group's actual
returned memory using the physical scheduler's original width and address. -/
def ReturnedDelivery.receivedRows (f : Delivery) (g : SharedRows.Layout)
    (group : Fin q → Fin (R+1)) (p : Symbols q) : List Bool :=
  receivedWord (H (group p.val.1)).history.val.2.2 (g.view p.val.1 p.val.2)
    (f.row (g.rowIndex p.val.1 p.val.2)).width

variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}
variable {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

/-- The actual original table row has the declaration's two owners and exact
selector-plus-cut width, and both ordered banks contain its complete raw word. -/
theorem SharedWriters.declaredRows (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group) (p : Symbols q) :
    let x := p.val.1
    let y := p.val.2
    let row := f.row (g.rowIndex x y)
    let raw := f.receivedRows g group p
    row.first = (group x).val ∧ row.second = (group y).val ∧
    raw.length = SharedRows.reserved blocks K h decl p ∧
    Resident (pairRegion g) (H (group x)).history.val.2.2 (g.view x y) raw ∧
    Resident (pairRegion g) (H (group y)).history.val.2.2 (g.view y x) raw := by
  intro x y row raw
  have ylt : y.val < g.groups := frame.groups ▸ y.isLt
  obtain ⟨first,second,width⟩ := writer.fields anchor p.property ylt
  have fx := first.trans (frame.owners x)
  have fy := second.trans (frame.owners y)
  exact ⟨fx,fy,(receivedWord_length ..).trans (width.trans (frame.toDeclarationFields.width p)),
    writer.pair_resident (group x) (group y) p.property ylt fx fy⟩

/-- The checked selector prefixes and pair declarations force a unique physical
payload for all received RAM words simultaneously. No choice is made per
ordered endpoint. -/
theorem SharedWriters.decode_received (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (selectors : ∀ p : Symbols q, (decodeSelectors a K h (packetVisits blocks decl.1 p).length
      ((f.receivedRows g group p).take (rowSelectorBits a q blocks K h decl.1 (Sym2.mk p.val.1 p.val.2)))).isSome)
    (declaration : ∀ select : Packet a q blocks → Selector a K h,
      (∀ p : Symbols q, (f.receivedRows g group p).take
        (rowSelectorBits a q blocks K h decl.1 (Sym2.mk p.val.1 p.val.2)) = commonSelectors select decl.1 p) →
      passesLengths b s select decl) :
    ∃! x : DeclaredShared blocks b h K s decl, sharedWords decl x = f.receivedRows g group := by
  apply (sharedWords_iff decl _).mp
  exact ⟨fun p => (writer.declaredRows frame p).2.2.1,selectors,declaration⟩

/-- The two successive inputs to an owned strict-row packet and singleton
scatter are resident at their actual ordered pair address in its team's RAM.
The supplied and singleton words may contain arbitrary private values. -/
theorem SharedWriters.physical_streams (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (select : Packet a q blocks → Selector a K h) (pass : passesLengths b s select decl)
    (supply : (p : Packet a q blocks) → (e : Cube.Edge (a+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot a q blocks (h*b) → Bool)
    (emits : sharedWords decl ⟨⟨select,pass⟩,fun _ => rowCrossValue supply single⟩ = f.receivedRows g group)
    (p : Symbols q) (high : Bool) :
    let x := p.val.1
    let y := p.val.2
    let u := if high then group y else group x
    let base := if high then g.view y x else g.view x y
    let sel := commonSelectors select decl.1 p
    Resident (pairRegion g) (H u).history.val.2.2 base sel ∧
      Resident (pairRegion g) (H u).history.val.2.2 (base+sel.length)
        (commonCrossings b decl.1 p select supply single) := by
  intro x y u base sel
  let cross := commonCrossings b decl.1 p select supply single
  have resident : Resident (pairRegion g) (H u).history.val.2.2 base (f.receivedRows g group p) := by
    have pair := (writer.declaredRows frame p).2.2.2
    cases high
    · exact pair.1
    · exact pair.2
  have raw : sel++cross = f.receivedRows g group p := by
    rw [show cross = (rowCrossKeys b s select decl.1 p).map (rowCrossValue supply single) from commonCrossings_eq_keys ..]
    exact congrFun emits p
  rw [← raw] at resident
  constructor
  · simpa only [List.length_nil,Nat.add_zero] using
      Resident.slice [] sel cross (by simpa only [List.nil_append] using resident :
        Resident (pairRegion g) (H u).history.val.2.2 base ([]++sel++cross))
  · exact Resident.slice sel cross [] (by simpa only [List.append_nil] using resident)

end TeamContraction

end BorderVNP
end Computability
end OAI
