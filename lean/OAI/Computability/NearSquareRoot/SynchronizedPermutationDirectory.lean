import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectoryHeaders
import OAI.Computability.NearSquareRoot.SynchronizedBlockPermutationTable
import OAI.Computability.NearSquareRoot.SynchronizedRoutingBenes
import OAI.Computability.NearSquareRoot.FixedLayerTickets
import OAI.Computability.NearSquareRoot.PrecisionSlotSchedule
import OAI.Computability.NearSquareRoot.CRTTableInputRows

/-! # Generating the complete block permutation directory of a directed row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermDirectory

open IntegerMultiplication Code Strip Staff SynchronizedBorrowing SynchronizedLayers.ScheduleProgram
open PermHeader

abbrev Summary := Tally × Tally × Tally
abbrev Live := Summary × AxisFields × Bool × SlotDescriptor
abbrev BlockInput := Block × Bool × Option SlotDescriptor
abbrev Entry := Tally × Benes.RawTable
abbrev Query := Bool × Tally × Tally

private def input (X : Type) [Codec X] : Regime X := ⟨Code.size,send,Dom.base _⟩

private theorem num {X : Type} [Codec X] (f : X → Tally) (F : Poly f) :
    Realizes (input X) (fun x => (f x).length) := by
  change Poly (fun x => tally (f x).length)
  simpa only [recover_tally] using F

/-- The dimensions of an actual batch, computed also on a malformed batch field
by reduction modulo the fifteen labels. -/
def measures (p : Tally × Tally) : Tally × Tally :=
  let b : Fin 15 := ⟨p.2.length % 15,Nat.mod_lt _ (by decide)⟩
  (tally (first p.1.length b), tally (SynchronizedBorrowing.size p.1.length b))

theorem measures_poly : Poly measures := by
  have B := num (fun p : Tally × Tally => p.1) Easy.fst.poly
  have J := (num (fun p : Tally × Tally => p.2) Easy.snd.poly).rem (.fix 15)
  let b (p : Tally × Tally) : Fin 15 := ⟨p.2.length % 15,Nat.mod_lt _ (by decide)⟩
  exact (Regime.Has.pair (first_realizes (batch := b) B J) (size_realizes (batch := b) B J))

def summary (g : Block) : Summary := (width g, volume g, low g)

private theorem summary_poly : Poly summary := width_poly.pair (volume_poly.pair low_poly)

def unaryPadding (f : AxisFields) : Tally := tally (f.1.2.length - f.1.1.length)

private theorem padding_poly : Poly unaryPadding :=
  (num (fun f : AxisFields => f.1.2) (by fun_prop)).minused (num (fun f : AxisFields => f.1.1) (by fun_prop))

/-- All scalar header fields needed for either the direct or the routed opcode.
The same borrowing extent is used on both sides. -/
def seeds (p : Live) : TableQuery × ((RoutingTable.Strides × RoutingTable.Dimensions) × Tally) :=
  let g := p.1
  let f := p.2.1
  let z := p.2.2.2
  let b := measures (f.2.2.2,z.1.2.1)
  let shape := (b,f.1.1,f.2.2.1)
  (((f.2.1.1,(f.2.1.2,z.1.2.2.1,z.1.2.2.2.1),shape,f.1.2,[]),g.2.1,g.1),
    (((f.2.1.1,f.1.2),g.2.2),(shape,f.2.2.2,unaryPadding f)),g.1)

theorem seeds_poly : Poly seeds := by
  have H : Poly (fun p : Live => measures (p.2.1.2.2.2,p.2.2.2.1.2.1)) :=
    (show Easy _ by fun_prop).poly.compose measures_poly
  have H' : Poly (fun p : Live => unaryPadding p.2.1) := (show Easy _ by fun_prop).poly.compose padding_poly
  let pack (q : Live × (Tally × Tally) × Tally) : TableQuery × ((RoutingTable.Strides × RoutingTable.Dimensions) × Tally) :=
    let g := q.1.1
    let f := q.1.2.1
    let z := q.1.2.2.2
    let shape := (q.2.1,f.1.1,f.2.2.1)
    (((f.2.1.1,(f.2.1.2,z.1.2.2.1,z.1.2.2.2.1),shape,f.1.2,[]),g.2.1,g.1),
      (((f.2.1.1,f.1.2),g.2.2),(shape,f.2.2.2,q.2.2)),g.1)
  have F : Easy pack := by unfold pack; fun_prop
  exact (Poly.identity.pair (H.pair H')).compose F.poly

/-- For a forward row the matrix reads from its permutation, hence the table
sends to the inverse. Adjoint rows exchange the directed routing tables. -/
def liveTable (p : Live) : Benes.RawTable :=
  let z := p.2.2.2
  let h := seeds p
  if z.2.length = 0 then portTable h.1
  else
    let t := RoutingTable.rawRouting h.2
    if z.2.length = 1 then bif p.2.2.1 then t.1 else t.2
    else bif p.2.2.1 then t.2 else t.1

private theorem micro_test (n : ℕ) : Poly (fun p : Live => decide (p.2.2.2.2.length = n)) := by
  have E := (show Easy (fun p : Live => (p.2.2.2.2,tally n)) by fun_prop).compose
    (Iter.linked (X := Unit) (Y := Unit))
  simpa using E.poly

theorem liveTable_poly : Poly liveTable := by
  have direct := seeds_poly.fstCompose.compose portTable_poly
  have both := seeds_poly.sndCompose.compose RoutingTable.rawRouting_poly
  have d : Poly (fun p : Live => p.2.2.1) := by fun_prop
  have P := Poly.choose (micro_test 0) direct (Poly.choose (micro_test 1)
    (Poly.choose d both.fstCompose both.sndCompose) (Poly.choose d both.sndCompose both.fstCompose))
  change Poly (fun p => liveTable p)
  simpa only [liveTable,Bool.cond_decide] using P

/-- The local block query receives an optional slot from the physical row.
Unset fields emit the identity graph on the full charged block volume. -/
def blockEntry (p : BlockInput) : Entry :=
  (width p.1, match p.2.2 with
    | some z => liveTable (summary p.1,fields (p.1,z.1.1),p.2.1,z)
    | none => idlePortTable (volume p.1,width p.1))

theorem blockEntry_poly : Poly blockEntry := by
  have Z : Easy (fun o : Option SlotDescriptor => o.elim default id) := PhaseTable.easyOption default id Easy.identity
  let z (p : BlockInput) := p.2.2.elim default id
  have V : Poly z := (show Easy (fun p : BlockInput => p.2.2) by fun_prop).poly.compose Z.poly
  have G := (Easy.fst (X := Block) (Y := Bool × Option SlotDescriptor)).poly
  have D : Poly (fun p : BlockInput => p.2.1) := by fun_prop
  have F := (G.pair V.fstCompose.fstCompose).compose fields_poly
  have active := ((G.compose summary_poly).pair (F.pair (D.pair V))).compose liveTable_poly
  have idle := ((G.compose volume_poly).pair (G.compose width_poly)).compose idlePortTable_poly
  have sel : Poly (fun p : BlockInput => p.2.2.elim false (fun _ => true)) :=
    (show Easy (fun p : BlockInput => p.2.2) by fun_prop).poly.compose
      (PhaseTable.easyOption false (fun _ => true) (Easy.const _)).poly
  have P := (G.compose width_poly).pair (Poly.choose sel active idle)
  convert P using 1
  funext p
  cases h : p.2.2 <;> simp [blockEntry,h,z]

abbrev Directed := Bool × Row SlotDescriptor

/-- Prepare one block, bypassing other row kinds with the identity. -/
def fromRow (p : Directed × (Tally × Block)) : Entry :=
  blockEntry (p.2.2,p.1.1,if p.1.2.1 = (false,false) then readBlock p.1.2 p.2.1.length else none)

theorem fromRow_poly : Poly fromRow := by
  let h := input (Directed × (Tally × Block))
  have H : h.Has (fun p => p.1.2) := (show Poly (fun p : Directed × (Tally × Block) => p.1.2) by fun_prop)
  have I := num (fun p : Directed × (Tally × Block) => p.2.1) (by fun_prop)
  have R := PhaseTable.readBlockAvailable H I
  have B : Easy (fun c : Bool × Bool => decide (c = (false,false))) := Easy.finite _
  have test : Poly (fun p : Directed × (Tally × Block) => decide (p.1.2.1 = (false,false))) :=
    (show Easy _ by fun_prop).poly.compose B.poly
  have read : Poly (fun p : Directed × (Tally × Block) =>
      if p.1.2.1 = (false,false) then readBlock p.1.2 p.2.1.length else none) := by
    simpa only [Bool.cond_decide] using Poly.choose test R (Code.Poly.const (none : Option SlotDescriptor))
  exact ((show Poly (fun p : Directed × (Tally × Block) => p.2.2) by fun_prop).pair
    ((show Poly (fun p : Directed × (Tally × Block) => p.1.1) by fun_prop).pair read)).compose blockEntry_poly

private def indexed (gs : List Block) := zipFair [] ([] : Block) (Iter.lineup (ruler gs), gs)

private theorem indexed_poly : Poly indexed :=
  (((Easy.ruler (Easy.identity (X := List Block))).poly.compose Iter.poly_line).pair Poly.identity).compose
    (easy_zip [] ([] : Block)).poly

/-- The low-block-first directory for the selected directed schedule index. -/
def directory (q : Query) : List Entry :=
  let r := Iter.pick (default : Directed) (directedPlan (q.1,q.2.1),q.2.2)
  (indexed (groups q.2.1)).map fun g => fromRow (r,g)

theorem directory_poly : Poly directory := by
  have R := ((show Easy (fun q : Query => (q.1,q.2.1)) by fun_prop).poly.compose directedPlan_poly).pair
    (show Poly (fun q : Query => q.2.2) by fun_prop)
  have T := R.compose (Iter.facile (default : Directed)).poly
  have S := (show Poly (fun q : Query => q.2.1) by fun_prop).compose (groups_poly.compose indexed_poly)
  exact (T.pair S).compose (Poly.push default default fromRow_poly)

theorem directory_machine : PolyTreeMachine Code.size send (fun q => send (directory q)) :=
  polyTreeMachine_of_BT (directory_poly.on (Dom.base _)) (Dom.base _)

theorem directory_entry {k : ℕ} (dir : Bool) (s : Fin (directedPlan (dir,tally k)).length)
    (b : Fin ((CoprimeBox.box k).length/4)) :
    let r := (directedPlan (dir,tally k))[s.val]
    (directory (dir,tally k,tally s.val))[b.val]? =
      some (fromRow (r,tally b.val, PermHeader.block (CoprimeBox.box k) b)) := by
  unfold directory
  simp only [Iter.search _ _ _ s.isLt, groups_eq, indexed]
  rw [CRTTable.zipFair_eq_zip]
  rotate_left
  · simp
  rw [List.getElem?_eq_getElem (by simp)]
  simp [Iter.lineup]

theorem directory_length (q : Query) : (directory q).length = (groups q.2.1).length := by
  simp only [directory, List.length_map, indexed]
  rw [CRTTable.zipFair_eq_zip] <;> simp

/-- All row kinds use the same ordered physical block widths. -/
theorem directory_widths (q : Query) : (directory q).map Prod.fst = (groups q.2.1).map width := by
  unfold directory indexed
  rw [CRTTable.zipFair_eq_zip _ _ _ _ (by simp)]
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.getElem_map,List.getElem_zip]
    rfl

end ShortFourier.BatchWord.PermDirectory

end NearSquareRoot
end Computability
end OAI
