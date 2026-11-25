import OAI.Hierarchy.DescentPaidSweepBill
import OAI.Hierarchy.DescentPaidSweepRun

namespace OAI
/-! # Literal ticks and printed hardware for the charged-mask and actor sweeps -/
namespace Hierarchy.DescentPaidResidentCount.Sweep
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask DescentOrdinaryAtomFieldRAM.ROM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescentStaticWordColumn
noncomputable section

private theorem names_columns (w rows W : ℕ) (es : List Expr) (bound : ∀ e∈es,e.work≤W) (base : ℕ) :
    names (ProtocolRAM.program w (ProbeStage.Native.columns rows base es))≤15+es.length*(11+4*W) :=by
  induction es generalizing base with
  | nil=>
    simp [ProbeStage.Native.columns,ProtocolRAM.program,names_scan,Expr.work]
  | cons e es ih=>
    have head:=bound e (List.mem_cons_self ..)
    have tail:=ih (fun t ht=>bound t (List.mem_cons_of_mem _ ht)) (base+rows)
    simp only [ProbeStage.Native.columns,ProtocolRAM.program,Pass.procedure,names_seq,names_scan,
      List.length_cons,Nat.succ_mul] at *
    omega

theorem tariff {n p : ℕ} (base D cap b H G M : ℕ) (labels : Fin p→ Cell n) (ids counts : Expr) (w : ℕ) :
    ticks base D cap b H G M labels ids counts+
      7*names (Sweep.program base D cap b H G M labels ids counts w) ≤
    2*tableBill ((p*2)*2^maskBits D cap n M)+tableBill (2*2^sumBits D cap b M)+
      columnBill p (rowCount H G M) (ids.work+counts.work+23)+columnBill p (rowCount H G M) (ids.work+12) :=by
  let es₁:=List.ofFn (job base D cap b M labels ids counts)
  let es₂:=List.ofFn (Presence.expr labels (actors D cap) M (actorBase base p D cap b n H G M) ids)
  have h₁ : ∀e∈es₁,e.work≤ ids.work+counts.work+23 :=by
    intro e h;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
    exact (job_work ..).le
  have h₂ : ∀e∈es₂,e.work≤ ids.work+12 :=by
    intro e h;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h
    rw [Presence.expr,DescentPackedZip.work]
    change ids.work+1+11≤ ids.work+12
    omega
  let x:=(paidBank base p D cap b n H G M).base
  let y:=(aliveBank base p D cap b n H G M).base
  have t₁:=ProbeStage.Native.columns_clock (rowCount H G M) x _ es₁ h₁
  have t₂:=ProbeStage.Native.columns_clock (rowCount H G M) y _ es₂ h₂
  have a₁:=names_columns w (rowCount H G M) _ es₁ h₁ x
  have a₂:=names_columns w (rowCount H G M) _ es₂ h₂ y
  have length₁ : es₁.length=p:=List.length_ofFn
  have length₂ : es₂.length=p:=List.length_ofFn
  simp only [ticks,paidClock,Sweep.program,paidCode,names_seq,DescentOrdinaryAtomFieldRAM.ROM.mount,names_mount,tableBill,columnBill]
  simp only [length₁,length₂] at t₁ t₂ a₁ a₂
  dsimp only [x,y,es₁,es₂] at t₁ t₂ a₁ a₂
  omega

end
end Hierarchy.DescentPaidResidentCount.Sweep

end OAI
