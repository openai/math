import OAI.Hierarchy.ProbeCatalystCashRead
import OAI.Hierarchy.ProtocolRAMCatalystArchiveTerminal

namespace OAI
/-! # Reading the owner of a charged port at its original calendar date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ColumnWires Calendar
open scoped Classical Fin.CommRing
variable {R C H E G : Type*} [Fintype C] [Fintype H] [Fintype E]
variable {balls D k count payload w : ℕ}

/-- A positive record supplies its native role and ball, and the abstract
owner of that original row is the geometric column/axis key. -/
theorem repair_positive_port (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k) ≤ D)
    (columns : R × C ↪ G) (keys : G × Fin k ↪ Fin count) (idle : Fin count)
    (read : Fin balls × Fin D → ℕ) (bounded : ∀z,read (portCell ballsAt bound z)≤payload)
    (i : Fin (balls*D)) (positive : 0 < (repairEntry ballsAt bound columns keys idle read bounded).bits i) :
    ∃ z, finProdFinEquiv (portCell ballsAt bound z)=i ∧
      (repairEntry ballsAt bound columns keys idle read bounded).owner i=keys (physical columns z) := by
  let cell := finProdFinEquiv.symm i
  change 0 < (decode ballsAt bound cell).elim 0 (fun _ => read cell) at positive
  cases eq : decode ballsAt bound cell with
  | none => simp only [eq,Option.elim_none,Nat.lt_irrefl] at positive
  | some z =>
    have index : finProdFinEquiv (portCell ballsAt bound z)=i :=
      (congrArg finProdFinEquiv (decode_spec ballsAt bound eq)).trans (finProdFinEquiv.apply_symm_apply i)
    refine ⟨z,index,?_⟩
    rw [←index]
    exact repair_owner ballsAt bound columns keys idle read bounded z

/-- Re-evaluate a positive physical port at its own event, then retain its
true bounded key in the terminal scatter. The physical expression is needed
only on original typed port occurrences. -/
theorem dated_repair_key {q goods : ℕ} (chart : Chart w q goods) (area : Arena) (initial : Memory w) (flag : ℕ)
    (mounted : Calendar.mounted chart (events chart.mesh) initial)
    (floor : ∀ t x,x<area.base chart.mesh t → protected chart x t)
    (time : Fin (events chart.mesh).length) (expr : Expr)
    (fit : expr.Fits w (area.base chart.mesh ((events chart.mesh).get time)))
    (high : area.base chart.mesh ((events chart.mesh).get time) ≤ flag)
    (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k) ≤ D)
    (columns : R × C ↪ G) (keys : G × Fin k ↪ Fin count) (idle : Fin count)
    (read : Fin balls × Fin D → ℕ) (bounded : ∀z,read (portCell ballsAt bound z)≤payload)
    (pos : 0<count) (width : count<2^w)
    (rom : ∀z,expr.eval (run chart ((events chart.mesh).take time.val) initial)
      ((finProdFinEquiv (portCell ballsAt bound z)).val:Word w)=((keys (physical columns z)).val:Word w))
    (i : Fin (balls*D)) (positive : 0 < (repairEntry ballsAt bound columns keys idle read bounded).bits i) :
    key pos (expr.eval (checkedOut chart flag initial) (i.val:Word w)) =
      (repairEntry ballsAt bound columns keys idle read bounded).owner i := by
  obtain ⟨z,index,owner⟩ := repair_positive_port ballsAt bound columns keys idle read bounded i positive
  have readKey := rom z
  rw [index] at readKey
  rw [dated_expr chart area initial flag mounted floor time expr _ fit high,readKey,key_true pos width,owner]

/-- A local positive-owner proof starts with ROM readings on the actual unpadded
geometric port table. Unreached roles and padding require no owner data. -/
inductive PortROM (expr : Expr) (m : Memory w) : Entry count payload → Prop where
  | feed : PortROM expr m (noneEntry count payload)
  | repair {R C H E G : Type} [Fintype C] [Fintype H] [Fintype E] {balls D k : ℕ}
      (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k) ≤ D)
      (columns : R × C ↪ G) (keys : G × Fin k ↪ Fin count) (idle : Fin count)
      (read : Fin balls × Fin D → ℕ) (bounded : ∀z,read (portCell ballsAt bound z)≤payload)
      (rom : ∀z,expr.eval m ((finProdFinEquiv (portCell ballsAt bound z)).val:Word w) =
        ((keys (physical columns z)).val:Word w)) :
      PortROM expr m (repairEntry ballsAt bound columns keys idle read bounded)

/-- The port-plan entry uses the actual signed cash at the commit snapshot.
The immutable owner operands can be read at the earlier event-entry snapshot. -/
theorem PortROM.of_readEntry {R₀ C₀ H₀ E₀ G₀ : Type} [Fintype C₀] [Fintype H₀] [Fintype E₀]
    {q K : ℕ} {stock : Calendar.StockCommit} {batch : Batch q D} {commit : Memory w}
    (layout : StockCommit.PortPlan stock batch commit balls) (ballsAt : R₀ ↪ Fin balls)
    (bound : Fintype.card (Role C₀ H₀ E₀ k)≤D) (columns : R₀ × C₀ ↪ G₀)
    (keys : G₀ × Fin k ↪ Fin count) (idle : Fin count) (positive : 0<K) (width : R₀→ℕ)
    (copies : ∀r,batch.copies ≤ copied K (width r) payload)
    (packet : ∀r,ballsAt r∈StockCommit.liveRows batch commit balls → ∀col axis,
      cashWord layout (ballsAt r,catalystPort bound (col,axis))≤batch.copies*width r)
    (expr : Expr) (dated : Memory w)
    (rom : ∀z,expr.eval dated ((finProdFinEquiv (portCell ballsAt bound z)).val:Word w) =
      ((keys (physical columns z)).val:Word w)) :
    PortROM expr dated (readEntry layout ballsAt bound columns keys idle positive width copies packet) := by
  unfold readEntry
  apply PortROM.repair
  exact rom

theorem PortROM.word {expr : Expr} {m : Memory w} {entry : Entry count payload}
    (installed : PortROM expr m entry) (i : Fin entry.rows) (pos : 0 < entry.bits i) :
    expr.eval m (i.val:Word w)=(entry.owner i).val := by
  cases installed with
  | feed => exact Fin.elim0 i
  | repair ballsAt bound columns keys idle read bounded rom =>
    obtain ⟨z,index,owner⟩ := repair_positive_port ballsAt bound columns keys idle read bounded i pos
    have decoded := rom z
    rw [index] at decoded
    simpa only [owner] using decoded

/-- Lift original typed inputs at each actual date to the positive-site
identity required by the native terminal reconciliation. -/
theorem nativeSite_from_portROM {q d : ℕ} (chart : Chart w q d) (area : Arena) (initial : Memory w)
    (flag : ℕ) (L : OwnerLedger) (issued : Attempt → Entry count payload)
    (pos : 0 < count) (size : count < 2^w) (mounted : Calendar.mounted chart (events chart.mesh) initial)
    (floor : ∀ t x,x < area.base chart.mesh t → protected chart x t)
    (fits : ∀ t : Fin (events chart.mesh).length,
      (L.term ((events chart.mesh).get t)).Fits w (area.base chart.mesh ((events chart.mesh).get t)))
    (high : ∀ t : Fin (events chart.mesh).length,area.base chart.mesh ((events chart.mesh).get t) ≤ flag)
    (plans : ∀ (t : Fin (events chart.mesh).length) (a : Attempt), (events chart.mesh).get t = .attempt a →
      PortROM (L.term (.attempt a)) (run chart ((events chart.mesh).take t.val) initial) (issued a))
    (j : Fin (recordCount chart.mesh issued)) (charged : 0 < debit chart.mesh issued j) :
    nativeSite L chart.mesh issued pos (checkedOut chart flag initial) j = site chart.mesh issued j := by
  let z := (rank chart.mesh issued).symm j
  let t := z.1
  let ev := (events chart.mesh).get t
  have ok : PortROM (L.term ev) (run chart ((events chart.mesh).take t.val) initial) (atTime chart.mesh issued t) := by
    change PortROM (L.term ev) _ (eventEntry issued ev)
    cases he : ev with
    | feed _ => exact .feed
    | attempt a => exact plans t a he
  have actual := ok.word z.2 charged
  change key pos ((L.term ev).eval (checkedOut chart flag initial) (z.2.val:Word w)) =
    (atTime chart.mesh issued t).owner z.2
  rw [dated_expr chart area initial flag mounted floor t (L.term ev) _ (fits t) (high t),actual,key_true pos size]

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
