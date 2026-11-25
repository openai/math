import OAI.Hierarchy.ProtocolRAMCatalystStripLedger
import OAI.Hierarchy.ProtocolRAMColumnReaderBounds
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Uniform native expression cost of reading a dated reserve owner -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Calendar AdaptiveProbe ProbeStage CoreBoard Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical

namespace CatalystArchive
open ColumnWires

def ownerWork (roles k columnCost : ℕ) :=
  3+2*(1+roles*(9+8*(3+k*(columnCost+1))))

theorem ownerPass_work {C H E : Type*} [Fintype C] [Fintype H] [Fintype E]
    (D k count base cells cost : ℕ) (column : C→Expr) (h : StockCommit.PortHeader)
    (cheap : ∀ i,(column i).work≤cost) :
    (clamp count (ownerPass (D:=D) (H:=H) (E:=E) (k:=k) base cells column h.fieldTerm h.ballTerm).term).work
      ≤ ownerWork D k cost := by
  let cap:=3+k*(cost+1)
  have table (r : Role C H E k) : (ownerExpr column r).work≤cap := by
    cases r with
    | catalyst i j =>
      have bound:=Nat.mul_le_mul_left k (Nat.add_le_add_right (cheap i) 1)
      simp only [ownerExpr,Expr.work,scale_work,cap]
      omega
    | _ => dsimp only [ownerExpr,Expr.work,cap];omega
  let xs:=fun i : Fin D=>PortPadding.extend
    (fun j=>((ownerExpr (H:=H) (E:=E) (k:=k) column) ((Fintype.equivFin (Role C H E k)).symm j)).atRow h.ballTerm)
    (.lit 0) i
  have bounded (i : Fin D) : (xs i).work≤8*cap := by
    dsimp only [xs,PortPadding.extend]
    split
    · apply (CatalogueRows.substitute_work _ h.ballTerm).trans
      change _*8≤8*cap
      exact (Nat.mul_le_mul_right 8 (table _)).trans_eq (Nat.mul_comm cap 8)
    · change 1≤8*cap
      dsimp only [cap];omega
  have selectBound:=BoughtSockets.choose_work_bound D 0 (8*cap) xs h.fieldTerm bounded
  change (chooseField D 0 xs h.fieldTerm).work≤1+D*(7+8*cap+2) at selectBound
  change (chooseField D 0 xs h.fieldTerm).work+1+(chooseField D 0 xs h.fieldTerm).work+1+1≤_
  dsimp only [ownerWork]
  rw [show 7+8*cap+2=9+8*cap by omega] at selectBound
  change _≤3+2*(1+D*(9+8*cap))
  omega

end CatalystArchive

namespace Calendar.StripChart
open CatalogueRows StripDirectory BoughtSockets PurchaseFrozen CatalystArchive ColumnWires
variable {z W k q depth : ℕ}
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
    (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

def ownerColumnCost (d k attempts : ℕ) :=
  max (56+8*ReportSockets.copies k attempts)
    (BoughtSockets.selectWork ((2*rounds d+1)*(2*k)) (70+15*ReportSockets.copies k attempts))

omit [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
theorem birth_column_work (p a : ℕ) (j : ChainStrip.Columns depth) :
    (birthColumn s c G p a j).work≤ownerColumnCost (2^W) k ((c.inject+c.cool)*c.outerFuel) := by
  unfold ownerColumnCost
  refine le_trans ?_ (le_max_right _ _)
  rw [←PurchaseFrozen.count_eq z (2^W) k]
  unfold birthColumn
  apply BoughtSockets.select_work
  intro i
  rw [ColumnROM.stage_work]
  change 2*9+52+ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel)*(9+6)≤_
  omega

theorem ledger_owner_work (arena : Arena) (count : ℕ) (ev : Event) :
    (clamp count ((ownerLedger s c b G F arena).term ev)).work≤
      ownerWork D k (ownerColumnCost (2^W) k ((c.inject+c.cool)*c.outerFuel)) := by
  cases ev with
  | feed _ =>
    dsimp only [ownerLedger,clamp,Expr.work,ownerWork]
    omega
  | attempt t =>
    let head (atTrial : Attempt) := header (z:=z) (d:=2^W) (k:=k) (q:=q) (depth:=depth) F
      (withPorts s c b G) atTrial
    let cost := ownerColumnCost (2^W) k ((c.inject+c.cool)*c.outerFuel)
    cases t with
    | outer p a =>
      let h := head (.outer p a)
      have cells (i : PayloadStrip.Columns (Stages z (2^W))) :
          ((payloadPortsAt s c G).column i).work≤56+8*ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel) :=
        ColumnROM.payload_work ..
      exact ownerPass_work (H:=Fin (PayloadStrip.edgeCount (Stages z (2^W))))
        (E:=PayloadStrip.Quotes (Stages z (2^W)) k ⊕ Empty) D k count 0 h.count cost
        (payloadPortsAt s c G).column h (fun i=>(cells i).trans (le_max_left _ _))
    | inner p a j t =>
      let h := head (.inner p a j t)
      exact ownerPass_work (H:=Fin (ChainStrip.edgeCount depth)) (E:=ChainStrip.Axes depth k ⊕ Unit)
        D k count 0 h.count cost (boughtPortsAt s c b G p a).column h (birth_column_work s c G p a)

def ownerRowFactor (d k degree depth ports : ℕ) :=
  ((2*rounds d+1)*(2*k))*degree^depth*ports

theorem ledger_owner_rows (arena : Arena) (ev : Event) :
    (ownerLedger s c b G F arena).rows ev≤ownerRowFactor (2^W) k s.sampler.degree depth D*2^z := by
  cases ev with
  | feed _ => exact Nat.zero_le _
  | attempt t =>
    change (PurchaseFrozen.count z (2^W) k * PurchaseFrozen.paths z s.sampler.degree depth) * D ≤ _
    rw [PurchaseFrozen.count_eq]
    dsimp only [PurchaseFrozen.paths, ownerRowFactor]
    apply Nat.le_of_eq
    ac_rfl

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
