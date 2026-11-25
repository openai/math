import OAI.Hierarchy.GridSelectorPadding
import OAI.Hierarchy.TraceAdmissionController
import OAI.ThreeFlat.Diagonal.NavigationTerminalWindow
import OAI.ThreeFlat.Diagonal.TraceTerminalEdges

namespace OAI
/-! # Closing an actual grid history visit on its entire selected tape -/

noncomputable section
namespace Hierarchy.GridSelector
open ThreeFlat RAM Diagonal Diagonal.HistoryContraction
open Diagonal.PhysicalStage Diagonal.NavigationPass Diagonal.NavigationDirectory Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {S : Shape}

/-- The native histogram scanner inspects the first fixed-width block. Every
legal history has its entire encoding in that block, so appending the rest
of the physical tape preserves *which* history was selected. -/
theorem short_read (P : Plan F S) (C : P.Codes) (raw : List Bool) (cut : ℕ)
    (bound : ∀ h,(P.write C h).length≤cut) :
    (P.read C (raw.take cut)).isSome ↔ (P.read C raw).isSome := by
  constructor
  · rintro yes
    obtain ⟨⟨h,rest⟩,hit⟩ := Option.isSome_iff_exists.mp yes
    have old := P.write_read C _ h rest hit
    have original : raw = P.write C h ++ (rest++raw.drop cut) := by
      calc
        raw = raw.take cut++raw.drop cut := (List.take_append_drop ..).symm
        _ = _ := by rw [old,List.append_assoc]
    rw [original,P.read_write]; rfl
  · rintro yes
    obtain ⟨⟨h,rest⟩,hit⟩ := Option.isSome_iff_exists.mp yes
    rw [P.write_read C _ h rest hit,List.take_append,List.take_of_length_le (bound h),P.read_write]
    rfl

theorem full_read_of_endsAt {d l : ℕ} {A : State d l} (r : Run F A) (E : r.Records)
    (xs : List Bool) (cut H : ℕ) (fixed : ∀ h,(r.plan.write (r.codes E) h).length=H)
    (v : Run.WireLayer) (receipt : r.EndsAt E (xs.take cut) v ((xs.take cut).drop H)) :
    r.EndsAt E xs v (xs.drop H) := by
  obtain ⟨h,parsed,terminal⟩ := receipt
  have old := r.plan.write_read _ _ h _ parsed
  have eq : xs=r.plan.write (r.codes E) h ++ ((xs.take cut).drop H ++ xs.drop cut) := by
    calc
      xs = xs.take cut++xs.drop cut := (List.take_append_drop ..).symm
      _ = (r.plan.write (r.codes E) h ++ (xs.take cut).drop H) ++ xs.drop cut :=
        congrArg (fun front : List Bool => front ++ xs.drop cut) old
      _ = _ := List.append_assoc ..
  have remove (front tail : List Bool) (size : front.length=H) : (front++tail).drop H=tail := by
    rw [←size,List.drop_left]
  have suffix := (congrArg (List.drop H) eq).trans (remove _ _ (fixed h))
  refine ⟨h,?_,terminal⟩
  calc
    _ = r.plan.read (r.codes E) (r.plan.write (r.codes E) h ++ ((xs.take cut).drop H ++ xs.drop cut)) :=
      congrArg (r.plan.read (r.codes E)) eq
    _ = _ := by rw [r.plan.read_write,←suffix]

/-- Equivalence with the independently implemented native padded terminal parser. -/
theorem read_shared (P : Plan F S) (C : P.Codes) (bits : P.History→ℕ) (cap : ℕ)
    (s : List Bool) (len : s.length=cap) :
    (P.decodeShared C bits cap s).isSome ↔ (read P C bits cap s).isSome := by
  cases hit : P.read C s with
  | none => simp [Plan.decodeShared,read,hit]
  | some z =>
    obtain ⟨h,rest⟩ := z
    rw [P.decodeShared_suffix C bits cap s h rest hit len]
    have total := congrArg List.length (P.write_read C s h rest hit)
    simp only [len,List.length_append] at total
    unfold read
    rw [hit]
    change _ ↔ (if len : bits h ≤ rest.length then
      if rest.drop (bits h)=List.replicate (cap-((P.write C h).length+bits h)) false then
        some (⟨h,readBits rest len⟩ : Trace P bits) else none else none).isSome
    by_cases hl : bits h ≤ rest.length
    · rw [dite_eq_left hl]
      have remain : cap-((P.write C h).length+bits h)=rest.length-bits h := by omega
      rw [remain]
      have agree := padded_iff rest (lo:=bits h) rfl
      change (_ ∧ _) ↔ (if rest.drop (bits h)=List.replicate (rest.length-bits h) false then
        some (⟨h,readBits rest hl⟩ : Trace P bits) else none).isSome
      split_ifs with pad
      · exact ⟨fun _=>rfl,fun _=>⟨hl,agree.mp pad⟩⟩
      · exact ⟨fun good=>(pad (agree.mpr good.2)).elim,by simp⟩
    · simp [hl]

/-- The final native `TerminalWireArchive.program` scans real terminal widths,
publishes their prefix directory, checks the original bits and returns at every
legal selector. The achieved typed history and its terminal state come from the
earlier native scanner's actual `EndsAt` receipt on the bounded prefix. -/
theorem terminal_visit {W stages : ℕ} (a : Archive) (P : Program F stages) (rem : ℕ)
    (X : State (2^stages) (P.charge+rem)) (field : FieldCode F W) (E : (P.run rem X).Records)
    (source : ℕ→Bool) (baseMem m : Memory W) (v : Run.WireLayer) (cut : ℕ) :
    let r := P.run rem X
    let ss := P.directory rem (Fintype.card X.Base)
    let edges := P.finalEdges rem (Fintype.card X.Base)
    let _c := finish a.K ss a.cursor
    let x := a.terminal ss edges W
    let bits := r.readTerminal (fun A=>A.widthSum)
    let raw := List.ofFn (fun i : Fin a.pairCapacity=>source i.val)
    let H := W*a.histWords ss
    (∀ h,(r.plan.write (r.codes E) h).length=H) →
    r.EndsAt E (raw.take cut) v ((raw.take cut).drop H) →
    a.Visit ss edges source (a.control:Word W) ss v.state m →
    a.cursor.header=a.seed+64 → a.seed+(a.directory ss edges W).length<2^W →
    a.TerminalRoom ss edges W → a.RawWindow ss source baseMem →
    (∀ addr, addr<a.seed → m addr=baseMem addr) → 1<2^W →
    TickStageSpec.Admission field (TerminalWireArchive.program (W:=W) x).block
      (TerminalWireArchive.program x).publicData (·=m)
      (fun _ => (read r.plan (r.codes E) bits a.pairCapacity raw).isSome)
      (fun _ out=>out=TerminalWireArchive.image x m) (Archive.terminalTime x) := by
  intro r ss edges _c x bits raw H fixed receipt visit head fits room window before two
  obtain ⟨h,parse,endState⟩ := full_read_of_endsAt r E raw cut H fixed v receipt
  have grade : edges=v.state.edgeCount := by rw [←endState]; exact (P.finalEdges_eq rem X h).symm
  have width : v.state.widthSum=bits h := by rw [←endState]; exact r.terminalLayer_width h
  have summed : x.widthBase+x.edges≤x.prefixBase := by
    change _c.width+edges≤_c.heap; rw [grade]; exact visit.widthBound
  have hle : H≤a.pairCapacity := by
    have parsed := congrArg List.length (r.plan.write_read _ _ h _ parse)
    simp only [raw,List.length_ofFn,List.length_append,fixed h] at parsed
    omega
  have old : x.oldSource+x.capacity≤x.prefixBase := by
    change a.oldHistory+H+(a.pairCapacity-H)≤_c.heap
    rw [Nat.add_assoc,Nat.add_sub_of_le hle]
    exact window.old.trans room.seed
  have newBank : x.newSource+x.capacity≤x.prefixBase := by
    change a.newHistory+H+(a.pairCapacity-H)≤_c.heap
    rw [Nat.add_assoc,Nat.add_sub_of_le hle]
    exact window.fresh.trans room.seed
  intro labels registers slots machine
  refine RAM.TickStageSpec.Admission.mono
    (fun {labels registers slots} M =>
      a.terminal_admission ss edges r.plan (r.codes E) bits raw (raw.drop H) h
        parse List.length_ofFn field m source v.state _ visit.live head fits room.bounds room.header
        room.control summed (window.phase.trans_le room.seed) old newBank (window.terminal edges two before)
        (by simp [Archive.terminal,raw,H]) rfl grade width visit.stored M)
    (fun _ same => same) ?_ (fun _ _ _ _ same => same) le_rfl machine
  exact fun _ _ => (read_shared r.plan (r.codes E) bits a.pairCapacity raw List.length_ofFn).symm

theorem terminal_price (a : Archive) (ss : List Stage) (edges W : ℕ) :
    Archive.terminalTime (a.terminal ss edges W)≤500*(edges+a.pairCapacity+2) := by
  let x := a.terminal ss edges W
  have pp : (TerminalWireArchive.prefixWord x).work≤100 := of_decide_eq_true rfl
  have cc : (TerminalWireArchive.checkWord x).work≤100 := of_decide_eq_true rfl
  have a1 := Nat.mul_le_mul_left (edges+1) (show 2*(TerminalWireArchive.prefixWord x).work+4≤204 by omega)
  have a2 := Nat.mul_le_mul_left (x.capacity+1) (show 2*(TerminalWireArchive.checkWord x).work+4≤204 by omega)
  have small : x.capacity≤a.pairCapacity := Nat.sub_le _ _
  change (11+(edges+1)*(2*(TerminalWireArchive.prefixWord x).work+4))+
    (6+(x.capacity+1)*(2*(TerminalWireArchive.checkWord x).work+4))≤_
  omega

open HistoryStageBody.Physical (resources resources_seq resources_scan) in
theorem terminal_hardware (a : Archive) (ss : List Stage) (edges W : ℕ) :
    let p := TerminalWireArchive.program (W:=W) (a.terminal ss edges W)
    p.labels+p.registers+p.slots≤2000 := by
  let x := a.terminal ss edges W
  change resources (TerminalWireArchive.program (W:=W) x) ≤ 2000
  simp only [TerminalWireArchive.program,resources_seq,resources_scan,HeaderScan.binds_closed]
  change 18+4*(TerminalWireArchive.prefixWord x).work +
    ((9+(HeaderScan.closed (TerminalWireArchive.checkWord x) : DescriptorExpr.Term W 0 1).labels)+
      (4+(HeaderScan.closed (TerminalWireArchive.checkWord x) : DescriptorExpr.Term W 0 1).binds)+0) ≤ 2000
  rw [DescriptorExpr.Term.labels_eq,HeaderScan.binds_closed]
  have prefixSize : (TerminalWireArchive.prefixWord x).work≤100 := of_decide_eq_true rfl
  have checkSize : (TerminalWireArchive.checkWord x).work≤100 := of_decide_eq_true rfl
  omega

end Hierarchy.GridSelector
end

end OAI
