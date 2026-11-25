import OAI.Hierarchy.ProtocolRAMCalendarWhole
import OAI.Hierarchy.ProtocolRAMCalendarPriced

namespace OAI
/-! # The priced physical calendar from the private header to the terminal reporter -/

namespace Hierarchy.ProtocolRAM.Calendar.Whole.Priced

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe PurchaseStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w r edges z d k q goods : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}
variable (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (s : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)

local notation "C" => pricedInstalled c finish prices format feeds s idBase role ids
local notation "V" => markets c finish prices format
local notation "W" => wordBits z d copies

theorem cheap (flag : ℕ) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    CheapCode (Controller.program z d C flag s a count n reserve) :=
  Controller.cheap (z:=z) (d:=d) C flag s a count n reserve

theorem text_eq (flag : ℕ) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    text (Controller.program z d C flag s a count n reserve) =
      text (subdivisionProgram z d)+
        (15+((events (C).mesh).map (eventText C)).sum+rowText (historyFlag C (events (C).mesh))+
        (listText (ReserveUse.columns a s.banks count n reserve)+22)+sinkText s) :=
  Controller.text_eq (z:=z) (d:=d) C flag s a count n reserve

/-- The charged occurrence scan reads the very same metric table as the terminal
report. Its full row count is charged to every attempted decision. -/
theorem attempt_clock (t : Attempt) :
    let p := format t
    let b := enabledBatch ((C).layout t) (testedBoard ((p.atTime c finish prices t).failures) p.board)
    Calendar.ticks C (.attempt t) =
      (guard C t).clock+(((C).frozen t).ticks+(postTicks ((C).layout t) (repair C t)+
        (((p.labelSource s idBase (role t) (ids t)).pass p.occurrences).clock+
          (StockCommit.freshSegment p.pricedArea p.stockSource W b).ticks))) := rfl

theorem attempt_text (t : Attempt) :
    let p := format t
    let b := enabledBatch ((C).layout t) (testedBoard ((p.atTime c finish prices t).failures) p.board)
    eventText C (.attempt t) =
      rowText (guard C t).term+text ((C).frozen t).native+postText ((C).layout t) (repair C t)+
        (rowText ((p.labelSource s idBase (role t) (ids t)).pass p.occurrences).term+
          text (StockCommit.freshSegment p.pricedArea p.stockSource W b).native) := by
  dsimp only
  exact congrArg (fun x=>rowText (guard C t).term+text ((C).frozen t).native+
    postText ((C).layout t) (repair C t)+x) ((format t).priced_text s idBase (role t) (ids t) _)

omit [Fintype I] [Fintype J] in
theorem exec {size n count : ℕ} (layout : Boot.Layout V size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag : ℕ)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count)
    (scheduled : mounted C (events (C).mesh) (Boot.booted V size words))
    (fit : (historyFlag C (events (C).mesh)).Fits W flag) (room : flag+1<2^W)
    (actual : Reconciliation s a reserve site debit e ci cj (checkedOut C flag (Boot.booted V size words))) :
    let committed := ReserveUse.output a s.banks reserve site debit (checkedOut C flag (Boot.booted V size words))
    (Controller.program z d C flag s a count n reserve).Exec
      (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header V size words))
      (s.output committed e ci (fun j=>(cj j).val))
      (Controller.ticks z d C s count n) :=
  Controller.exec V C layout hd π words authentic flag s a reserve site debit e ci cj scheduled fit room actual

omit [Fintype I] [Fintype J] in
theorem run {size n count : ℕ} (layout : Boot.Layout V size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag : ℕ)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count) (state : Word W)
    (scheduled : mounted C (events (C).mesh) (Boot.booted V size words)) (ord : separated C (events (C).mesh))
    (fit : (historyFlag C (events (C).mesh)).Fits W flag) (room : flag+1<2^W)
    (actual : Reconciliation s a reserve site debit e ci cj (checkedOut C flag (Boot.booted V size words)))
    (below : flag<s.banks.reserved.base ∧ flag<s.banks.used.base ∧ flag<a.scratch ∧
      flag<s.banks.width.base ∧ flag<s.table ∧ flag<s.destination) :
    let initial := Computability.VPVNP.RAMMemory.initialMemory size (Boot.header V size words)
    let committed := ReserveUse.output a s.banks reserve site debit (checkedOut C flag (Boot.booted V size words))
    let M := machine (Controller.program z d C flag s a count n reserve) (flag:Word W)
    let out := s.output committed e ci (fun j=>(cj j).val)
    ∃ t≤Controller.ticks z d C s count n+2, ∃ term,
      advance M.program t (M.program.start state) initial=some (term,out) ∧
      M.program.step term=.finish (some (out flag)) ∧
      (out flag=0 ↔ admissible C (events (C).mesh) (Boot.booted V size words)) :=
  Controller.run V C layout hd π words authentic flag s a reserve site debit e ci cj state scheduled ord fit room actual below


end
end Hierarchy.ProtocolRAM.Calendar.Whole.Priced

end OAI
