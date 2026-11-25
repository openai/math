import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentEpochGrains
import OAI.Hierarchy.DescentEpochReset
import OAI.Hierarchy.DescentOrdinarySchedule
import OAI.Hierarchy.DescentEpochHistory

namespace OAI
/-! # Closing the common ordinary schedule with its issued reset -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentColonies DescentFineTerminals DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentHostDegree
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z w hist : ℕ}

theorem close_branch {W : MarkedWorld F d P bits} {D n h C f g cut tail : ℕ}
    (input : Reached W G q ε S k i z D w hist)
    (ctl : ResetRates G S k D n h C f g cut tail)
    (age : i<S.length) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (history : 6*hist≤w*(z*G.b)) :
    Nonempty (ClosedReset input ctl) := by
  rcases input with ⟨V, A, valid, rfl, rfl, rfl, rfl,
    order, vertex, edgeName, siteName⟩
  have cap : A.hist≤A.wire*(A.z*G.b)*A.cap := by
    have least : A.hist≤A.wire*(A.z*G.b) := by omega
    exact least.trans (Nat.le_mul_of_pos_right _ A.capPos)
  obtain ⟨Z,T,tickets,used,zk,unit,dim,width,graph,N,paid,z',w',hist',degree,capacity,site,block,hubFlag,frame,roster⟩ :=
    A.epoch_reset S valid ctl.board order (vertex.trans Fin.valEmbedding) ctl.base ctl.radix ctl.fixed
      ctl.height age budget ctl.fcut ctl.gk ctl.gain ctl.host ctl.cap ctl.fineCap ctl.seed ctl.degree
      ctl.enough (Nat.succ_pos _) ctl.bits_positive ctl.rows ctl.menu ctl.loss cap
  exact ⟨{
    count:=A.grainCount,count_eq:=rfl,fit:=A.grainCount_fit S valid,order:=order,order_eq:=rfl,
    reset:=Z,terminals:=T,age:=age,commonDepth:=used,keyWidth:=zk,tickets:=tickets,unit:=unit,dimension:=dim,width:=width,graph:=graph,frame:=frame,roster:=roster,
    raw:=N,rawGeometry:=⟨site,block⟩,rawHub:=hubFlag,valid:=paid,grain:=z',wire:=w',atoms:=hist',degree:=degree,capacity:=capacity}⟩

/-- The epoch assembled from these exact per-branch receipts. Its output normalization
includes both installed physical site and cable ordinals. -/
def periodEpoch {n h C f g cut tail : ℕ} (he : 0≤ε) (hu : 0≤q*w)
    (H : Histories F d P bits) (run : Schedule G he (u:=q*w) S.rounds H)
    (ctl : ResetRates G S k (atRound S.rounds) n h C f g cut tail) (positive : 0<z)
    (endReached : ∀c,Reached ((Schedule.finish G he run).state c) G q ε S k i z (atRound S.rounds) w hist)
    (b : ∀c,ClosedReset (endReached c) ctl) : Epoch H G hu he S.rounds h C (GroupStage.depthBound (atRound S.rounds) n f g) where
  subrounds := run
  grain := z*G.b
  positive := Nat.mul_pos positive G.base_pos
  count := fun c=>(b c).count
  fit := fun c=>(b c).fit
  order := fun c=>(b c).order
  reset := fun c=>(b c).reset
  terminals := fun c=>(b c).terminals
  tickets := fun c=>(b c).tickets
  reblock := fun c=>(b c).reblock

theorem periodEpoch_grains {n h C f g cut tail : ℕ} (he : 0≤ε) (hu : 0≤q*w)
    (H : Histories F d P bits) (run : Schedule G he (u:=q*w) S.rounds H)
    (ctl : ResetRates G S k (atRound S.rounds) n h C f g cut tail) (positive : 0<z)
    (endReached : ∀c,Reached ((Schedule.finish G he run).state c) G q ε S k i z (atRound S.rounds) w hist)
    (b : ∀c,ClosedReset (endReached c) ctl) (zRow : ℕ→ℕ) (issued : Schedule.Grains zRow run) (atStop : zRow S.rounds=z) :
    Epoch.Grains zRow ctl.board ctl.bitsR (periodEpoch he hu H run ctl positive endReached b) :=
  ⟨issued,congrArg (·*G.b) atStop.symm,(fun c=>(b c).unit),
    (fun c=>(b c).dimension),(fun c=>(b c).width),(fun c=>(b c).graph),(fun c=>(b c).cuts)⟩

/-- Close every possible current history with its own realized, priced router.
All branches share a fixed height and grain; their terminal worlds are the
actual reblocked outputs of this epoch. -/
theorem close_period {n h C f g cut tail : ℕ} (he : 0≤ε) (hu : 0≤q*w)
    (H : Histories F d P bits) (run : Schedule G he (u:=q*w) S.rounds H)
    (ctl : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (age : i<S.length) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<z) (history : 6*hist≤w*(z*G.b))
    (atEnd : ∀c,Nonempty (Reached ((Schedule.finish G he run).state c) G q ε S k i z (atRound S.rounds) w hist))
    (zRow : ℕ→ℕ) (issued : Schedule.Grains zRow run) (atStop : zRow S.rounds=z) :
    ∃E : Epoch H G hu he S.rounds h C (GroupStage.depthBound (atRound S.rounds) n f g),
      Epoch.Grains zRow ctl.board ctl.bitsR E ∧
      ∀c, Nonempty (Reached ((E.finish G hu he).state c) G q ε S k (i+1) z 3 w hist) := by
  let done := Schedule.finish G he run
  let b (c : done.Choice) := (close_branch (atEnd c).some ctl age budget history).some
  exact ⟨periodEpoch he hu H run ctl positive (fun c=>(atEnd c).some) b,
    periodEpoch_grains he hu H run ctl positive (fun c=>(atEnd c).some) b zRow issued atStop,
    fun c=>⟨(b c).next⟩⟩

end
end Hierarchy.DescentSixParty

end OAI
