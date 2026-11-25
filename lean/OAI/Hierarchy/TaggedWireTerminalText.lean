import OAI.Hierarchy.TaggedWireFixedTurnClock
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Instruction text for the eleven physical signed classifier columns -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure

private def lineText (n : ℕ) := 15+4*(11+4*(8*(4*n+18)+5))
def boardText (n m : ℕ) := lineText n+lineText m+(15+3*(11+4*(67+(4*n+18))))

private theorem four_text (L : Chart) (v : Bool→Socket) {n : ℕ} (ok : ∀s,(v s).Work n)
    (base rows : ℕ) (reported : Bool) (w : ℕ) : Native.text (native w base rows L v reported)≤lineText n := by
  have bounded (e : Expr) (he : e∈List.ofFn (field L v reported)) : e.work≤8*(4*n+18)+5 := by
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
    exact field_work L v ok reported i
  simpa only [native,passes,lineText,List.length_ofFn] using
    Native.columns_text w rows base (8*(4*n+18)+5) (List.ofFn (field L v reported)) bounded

theorem Board.terminal_text (b : Board) (stockStart : ℕ) (paid active reserve used : Bank)
    (w : ℕ) {n m : ℕ} (first : ∀s,(b.before s).Work n) (last : ∀s,(b.finish s).Work m) :
    Native.text (b.extended (Inventory.ofOriginal stockStart b.old paid active reserve used) w)≤boardText n m := by
  let I:=Inventory.ofOriginal stockStart b.old paid active reserve used
  have width : I.width.work=67:=rfl
  have source (e : Expr) (he : e∈List.ofFn (b.rawFields I)) : e.work≤67+(4*n+18) := by
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    fin_cases j
    · exact (socket_work b.chart _ (first false)).1.trans (Nat.le_add_left _ _)
    · exact (socket_work b.chart _ (first true)).1.trans (Nat.le_add_left _ _)
    · change I.width.work≤_
      rw [width];omega
  have extra:=Native.columns_text w b.old b.endAt _ (List.ofFn (b.rawFields I)) source
  simp only [List.length_ofFn] at extra
  simp only [Board.extended,Board.code,Native.text_seq]
  exact Nat.add_le_add (Nat.add_le_add (four_text b.chart b.before first _ _ false w)
    (four_text b.chart b.finish last _ _ true w)) extra

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups

theorem fixed_text (S : PurchaseSampler) (W k attempts depth : ℕ) :
    ∃ rate : ℕ,∀ (h R H : ℕ) (_order : Fin R≃Edges S h (2^W) k)
      (dir : Directory (reserved h W (copies k attempts)) H) (v : BoughtSockets.Directory attempts)
      (b : CatalogueRows.Board) (start out base bits siteBase superBase K G slots : ℕ)
      (paidBank active reserve used : Bank) (w : ℕ),
      let edges:=R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
      let z:=shape (R:=R) S dir edges
      let core:=CoreCatalogue.source base R bits siteBase superBase K G slots k attempts
      let paid:=paidInputs b (coreInputs base (z.free start) R bits superBase K k attempts)
        (boughtInputs v S h W k depth K)
      let board:=turnBoard (R:=R) S dir (edges:=edges) start out core paid
      Native.text (board.extended (Inventory.ofOriginal (z.stop start) board.old paidBank active reserve used) w)≤rate := by
  let u:=paidWidthWork W k attempts
  let n:=oldWork k u (coreWidthWork k attempts)
  refine ⟨boardText n u,?_⟩
  intro h R H order dir v b start out base bits siteBase superBase K G slots paidBank active reserve used w
  let edges:=R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
  let z:=shape (R:=R) S dir edges
  let core:=CoreCatalogue.source base R bits siteBase superBase K G slots k attempts
  let paid:=paidInputs b (coreInputs base (z.free start) R bits superBase K k attempts) (boughtInputs v S h W k depth K)
  let board:=turnBoard (R:=R) S dir (edges:=edges) start out core paid
  have p (s : Bool) : (board.finish s).Work u :=
    paid_work b v S h W k depth K base (z.free start) R bits superBase s
  have q (s : Bool) : (board.before s).Work n :=
    full_original_work (z.chart start) b v S start board.old (z.ext start) (z.axis start)
      base (z.free start) R bits siteBase superBase K G slots h W k depth s
  exact board.terminal_text (z.stop start) paidBank active reserve used w q p

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
end

end OAI
