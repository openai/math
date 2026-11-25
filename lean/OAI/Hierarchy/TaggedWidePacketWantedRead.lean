import OAI.Hierarchy.TaggedWidePacketWantedFields
import OAI.Hierarchy.TaggedWirePacketNeighbor

namespace OAI
/-! # The pre-release word in each original role's dated degree slot -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.PacketNeighbor
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
variable {S : ℕ} {s : Fin S}

theorem other_ne (p : (portGraph S).Port s) : s≠other p := by
  rcases p with ⟨⟨ch,b⟩,incident⟩
  cases b <;> simp only [portGraph,PortGraph.vertex] at incident <;> subst s
  · exact ch.property.ne
  · exact ch.property.ne.symm

theorem ordered_other (p : (portGraph S).Port s) : Probe.orderedEnds s (other p) (other_ne p)=p.val.1 := by
  rcases p with ⟨⟨ch,b⟩,incident⟩
  cases b <;> simp only [portGraph,PortGraph.vertex] at incident <;> subst s
  all_goals simp [Probe.orderedEnds,other,portGraph,PortGraph.vertex,ch.property,not_lt_of_ge ch.property.le]

/-- The endpoint lift re-sorts the physical chord when placement reverses its two parties. -/
def reached (a b : Fin S) (ne : a≠b) : (portGraph S).Port a :=
  if lt : a<b then ⟨(⟨(a,b),lt⟩,false),rfl⟩ else
    ⟨(⟨(b,a),lt_of_le_of_ne (le_of_not_gt lt) ne.symm⟩,true),rfl⟩

@[simp] theorem reached_other (a b : Fin S) (ne : a≠b) : other (reached a b ne)=b := by
  unfold reached;split <;> rfl

theorem reached_chord (a b : Fin S) (ne : a≠b) : (reached a b ne).val.1=Probe.orderedEnds a b ne := by
  unfold reached Probe.orderedEnds;split <;> rfl

def liftPort {L : ℕ} {i : Fin L} (place : Fin L↪Fin S) (p : (portGraph L).Port i) :
    (portGraph S).Port (place i) := reached (place i) (place (other p)) (place.injective.ne (other_ne p))

@[simp] theorem lift_other {L : ℕ} {i : Fin L} (place : Fin L↪Fin S) (p : (portGraph L).Port i) :
    other (liftPort place p)=place (other p) := reached_other ..

theorem lift_chord {L : ℕ} {i : Fin L} (place : Fin L↪Fin S) (p : (portGraph L).Port i) :
    (liftPort place p).val.1=Probe.physicalChord place p.val.1 := by
  rw [liftPort,reached_chord]
  rcases p with ⟨⟨ch,side⟩,inc⟩
  cases side <;> simp only [portGraph,PortGraph.vertex] at inc <;> subst i
  · rfl
  · exact Probe.orderedEnds_comm ..

end Hierarchy.WireTelescope.PacketNeighbor
namespace Hierarchy.ProbeStage.CoreBoard.SiteDirectory
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open AdaptiveProbe Probe WireTelescope ProtocolRAM Tagged
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {F E A : Type} [Field F] [Fintype E] [Nonempty E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]
variable {edge : E→Chord k} {req : A→E} {box : Set (E→ℝ)} {ε tree : ℝ} {N S W D K : ℕ}
    (M : FixedMenu F edge req box ε tree N) (copies : ℕ) (party : Fin k→Expr)
    (m : Memory W) (row : Word W) (place : Fin k↪Fin S) (s : Fin S)
    {total : (portGraph S).Port s→ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total)
    (width nbr : Fin D→Expr) (dated : PacketTurns.NeighborReads m row parts width nbr)
    (tag here : Expr) (choice : M.index)
local notation "released" => optionWidths (fun a : PositiveDemand req choice.val.val=>physicalChord place (edge (req a.val)))
    (fun _=>copies*(M.packet choice).width)

include dated in
theorem wantField_read (fits : 1+Fintype.card M.index≤2^W)
    (auth : (tag.eval m row).val=(Fintype.equivFin _ choice).val+1) (sites : S≤2^W)
    (measured : ∀i,(party i).eval m row=((place i).val:Word W)) (atSite : here.eval m row=(s.val:Word W)) (q : Fin D) :
    (wantField M copies party tag here (width q) (nbr q)).eval m row=
      ((parts.owner q).elim 0 (fun p=>if 0<parts.width q then released p.val.1 else 0) : Word W) := by
  rw [want_at M copies party m row tag here _ _ choice fits auth]
  have amount:=dated.widthAt q
  cases eq:parts.owner q with
  | none=>
    rw [wantFor_blank M copies party m row choice here _ _ (by simpa [PacketNeighbor.amount,eq] using amount)]
    rfl
  | some p=>
    simp only [Option.elim_some]
    by_cases zero:parts.width q=0
    · simp only [zero,lt_self_iff_false,ite_false]
      apply wantFor_blank
      simpa [PacketNeighbor.amount,eq,zero] using amount
    · have use:=Nat.pos_of_ne_zero zero
      rw [ite_eq_left use]
      have bound : parts.width q<2^W:=by simpa [PacketNeighbor.amount,eq] using dated.fits q
      have value : ((width q).eval m row).val=parts.width q := by
        rw [amount];simpa only [PacketNeighbor.amount,eq,Option.elim_some] using Fin.val_cast_of_lt bound
      have live : (width q).eval m row≠0:=fun empty=>zero (value.symm.trans (congrArg Fin.val empty))
      rw [wantFor_read M copies party m row choice here (width q) (nbr q) place s (PacketNeighbor.other p)
        (PacketNeighbor.other_ne p) live sites measured atSite (dated.siteAt q p eq use),PacketNeighbor.ordered_other]

end Hierarchy.ProbeStage.CoreBoard.SiteDirectory

end
end OAI
