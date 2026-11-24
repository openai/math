import OAI.Computability.VPVNP.CompressorTermWorkerDispatch
import OAI.Computability.VPVNP.CompressorSourceLaunch
import OAI.Computability.VPVNP.CompressorOnlineRowInverse

/-! # The physical row invariant at a compressor term selector

The fixed term table reads a demand row and writes its selected supply
coordinates. For any successful choice tape it preserves all demand
inputs, writes outside the scheduler frame, returns the next ordinal,
and satisfies the row-specific clock. The script recipe supplies its
actual bank from the current RAM.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermWorker

open BurstRAM TermRecordScan MotifGrid MotifBlocks MotifConversion MotifSelector Schedule OrdinalRun
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')
variable {d n : ℕ} (order : Fin d ≃ D) (supply : Fin n ≃ S) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)

private theorem call_catalog {W : Schedule.Pass} (eq : W = motifPass B order n) {w : ℕ}
    (addr : Fin 4 → BurstRAM.Word w) (f : ℕ) (s : BurstRAM.Word w) (mem : Memory w) (bs : List Bool) :
    let G := (W.table.instantiate w (fun i => motifData B order supply w addr (i.cast (congrArg Schedule.Pass.params eq)))).program
    execute G f (G.start s) mem bs = execute (program B order supply addr) f ((program B order supply addr).start s) mem bs := by
  subst W
  rfl

/-- Genuine local inverse for any catalog occurrence of the fixed term
worker, using its actual call-frame and event bound. -/
theorem workerStep {workers m M w cap fuel : ℕ} (C : Catalog workers) (j : Fin workers)
    (ports : Schedule.Ports w) (passEq : C j = motifPass B order n)
    (layout : Layout m d n w) (addr : Fin 4 → BurstRAM.Word w) (haddr : Addresses layout addr)
    (demand : Fin m → D → ℕ) (hD : ∀ i x, demand i x ≤ M)
    (width : frameFit B order supply hp hq + 4*Nat.clog 2 (M+1) ≤ w)
    (clock : budget B d n w M ≤ fuel) (hcap : fuel ≤ cap) (hstop : m < 2^w)
    (apart : ∀ i x, ControlCell (C j).params ports x → layout.Outside i x) :
    Online.WorkerStep ports j (catalogWords B order supply C j addr passEq) (m : BurstRAM.Word w) cap fuel
      (fun _ mem => Inputs order layout demand mem) := by
  intro st mem bs rep frame inv active source
  have hi : st.val < m := by
    change st.val < m % (2^w) at active
    rwa [Nat.mod_eq_of_lt hstop] at active
  let i : Fin m := ⟨st.val,hi⟩
  have stEq : (i.val : BurstRAM.Word w)=st := Fin.ext (Nat.mod_eq_of_lt st.isLt)
  have capBound := clock.trans hcap
  have concrete : execute (program B order supply addr) cap ((program B order supply addr).start st) mem bs = some rep :=
    (call_catalog B order supply passEq addr cap st mem bs).symm.trans source
  rw [← stEq] at concrete
  obtain ⟨next,inv',keep,_,short⟩ := (call_frame B order supply hp hq).choose_spec m M w width
    layout addr haddr demand hD cap capBound mem inv i bs rep concrete
  exact ⟨short.trans_le clock,_,next,ready_of_preserved C j ports frame (fun x hx => keep x (apart i x hx)),inv'⟩

open DescriptorSpace BlockPlanner SourceOnline SourceTransport
open private control_below from OAI.Computability.VPVNP.CompressorSourceOnline

/-- Construct the actual scheduler boundary certificate needed to invert a
term-selection row. The readable and writable term arenas begin after the
workspace directory. Only the public operand and width equations specific
to the physical motif remain at a use site. -/
noncomputable def rowStart {m M w cap fuel : ℕ} (A : Script) (outer : DescriptorSpace.Layout)
    (base : BurstRAM.Word w) (hg : arity A.catalog=outer.shape.arity) (hb : base.val=outer.base)
    (fit : levelStart outer 0 < 2^w) (mem : Memory w) (j : Fin A.size)
    (passEq : A.catalog j = motifPass B order n)
    (layout : TermRecordScan.Layout m d n w) (addr : Fin 4 → BurstRAM.Word w) (haddr : Addresses layout addr)
    (demand : Fin m → D → ℕ) (hD : ∀ i x, demand i x ≤ M)
    (width : frameFit B order supply hp hq+4*Nat.clog 2 (M+1) ≤ w)
    (clock : budget B d n w M ≤ fuel) (hstop : m < 2^w)
    (readable : ∀ i, levelStart outer 0 ≤ (layout.source i).val)
    (writable : ∀ i, levelStart outer 0 ≤ (layout.base i).val)
    (inputs : Inputs order layout demand mem)
    (stop : A.operand base mem j (A.visit j).stop = (m : BurstRAM.Word w))
    (args : ∀ i, A.operand base mem j ((A.visit j).params i) = catalogWords B order supply A.catalog j addr passEq i)
    (phase : (Online.calendar A.plan).phase (mem (Workspace.ports (arity A.catalog) base).ordinal.val).val = j.val)
    (room : (mem (Workspace.ports (arity A.catalog) base).ordinal.val).val < directoryRows outer)
    (active : mem (Workspace.ports (arity A.catalog) base).ordinal.val < mem (Workspace.ports (arity A.catalog) base).rows.val)
    (recipeCap : (A.plan.recipes j).2.code.length+1+2*(Online.N A.size A.size)+5 ≤ cap)
    (dataCap : fuel+3+4*((A.catalog j).params+1)+2*(Online.N A.size A.size)+5 ≤ cap) :
    Online.Run.RowStart A.plan (Workspace.ports (arity A.catalog) base) cap mem := by
  let ports := Workspace.ports (arity A.catalog) base
  let entry := Online.rowInput A.plan ports mem j
  let fresh := Directory.prepared A.catalog ports entry
  have launch := evaluated_launch A base outer hg hb fit mem j fuel [] room active
  have stored : Directory.words A.catalog ports j entry = catalogWords B order supply A.catalog j addr passEq :=
    launch.params.trans (funext args)
  have endWord : Directory.bound A.catalog ports entry = (m : BurstRAM.Word w) := launch.stop.trans stop
  have agree := OnlineFootprint.prepared A outer base hg hb fit mem j room
  have freshInput : Inputs order layout demand fresh := by
    intro i
    funext x
    obtain ⟨l,rfl⟩ := order.surjective x
    rw [DemandPreparation.demandAt_address order _ _ (layout.sourceFits i)]
    have hr := congrFun (inputs i) (order l)
    rw [DemandPreparation.demandAt_address order _ _ (layout.sourceFits i)] at hr
    exact (congrArg Fin.val (agree _ ((readable i).trans (Nat.le_add_right ..)))).symm.trans hr
  refine ⟨j,j,fuel,fun _ mem => Inputs order layout demand mem,phase,?_,?_,recipeCap,dataCap,?_,freshInput,?_⟩
  · change entry ports.ordinal.val < entry ports.rows.val
    rw [show entry ports.ordinal.val = mem ports.ordinal.val from launch.ordinal,
      show entry ports.rows.val = mem ports.rows.val from launch.rows]
    exact active
  · have hpos : 0 < budget B d n w M := by unfold budget; omega
    exact hpos.trans_le clock
  · change Ready A.catalog j ports (Directory.words A.catalog ports j entry) (Directory.bound A.catalog ports entry) fresh
    rw [stored,endWord]
    have hr : Ready A.catalog j ports (fun i => A.operand base mem j ((A.visit j).params i))
        (A.operand base mem j (A.visit j).stop) fresh := launch.ready
    exact ⟨hr.1,hr.2.1.trans stop,funext fun i => (congrFun hr.2.2 i).trans (args i)⟩
  · change Online.WorkerStep ports j (Directory.words A.catalog ports j entry) (Directory.bound A.catalog ports entry) cap fuel _
    rw [stored,endWord]
    exact workerStep B order supply hp hq A.catalog j ports passEq layout addr haddr demand hD width clock
      (by omega) hstop (fun i x hx => Or.inl ((control_below A outer base hg hb fit j x hx).trans_le (writable i)))

end CompressorRecords.TermWorker

end VPVNP
end Computability
end OAI
