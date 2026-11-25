import OAI.Hierarchy.DescentDatedResetBook
import OAI.Hierarchy.DescentEstimatorDateTariff

namespace OAI
/-! # One fixed physical estimator chart at each genuine reset age -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentPackedWalsh DescentCompiler DescentCompiler.TerminalScale DescentWalshPrecision
variable {F : Type} [Field F] (G : PoweredGadget F)

def numberedReset (S : AtomSchedule) (k tail age payload p f quota fullBudget ports rowBase pitch classes floor : ℕ) :
    Placement :=
  let m:=S.groupWidth k tail age+k
  let b:=S.localWalshBits p m f quota
  let l:=laneBits m payload b
  ⟨⟨S.hostSize age,ports,m-l,l,b,rowBase,pitch,f,fullBudget,classes⟩,floor⟩

namespace Placement
variable (P : Placement)

/-- All live old headers are below the actual mounted constants. The final one-past-address
bound therefore verifies every address used by the original physical oscillator and ballot. -/
theorem native_fits (h gain w : ℕ) (positive : 0<P.geo.bits)
    (lanes : laneBits (P.geo.high+P.geo.low) h P.geo.bits=P.geo.low)
    (lookup : gain+P.geo.bits*2^P.geo.low≤w)
    (bound : (P.estimator h gain positive).endAddress<2^w) :
    (P.estimator h gain positive).Fits w := by
  let E:=P.estimator h gain positive
  let N:=P.geo.hosts*((P.geo.high+P.geo.low)+1)+P.geo.hosts*P.geo.ports
  have rows : E.hosts=N:=by dsimp [E,estimator,N];ring
  have size : N≤pad N:=cover N
  have prefix₀ : E.origin≤E.start := (P.estimator_prefix h gain positive).trans (Nat.le_add_right ..)
  have start : E.start<2^w := by
    apply lt_of_le_of_lt _ bound
    rw [E.endAddress_eq]
    omega
  have depth : E.depthRows.base+E.depthRows.size≤E.origin := by
    change P.depthPage+pad N≤P.gainPage+pad N
    unfold gainPage
    omega
  have amount : E.gainRows.base+E.gainRows.size≤E.origin := by rfl
  have scanEnd : E.solveAt≤E.endAddress:=by
    change E.solveAt ≤ E.solveAt + E.dim*(3*2^E.dim+1) + 2^E.dim + 2^E.dim
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have pRoom : page E.hosts E.high≤E.endAddress:=by
    rw [E.endAddress_eq]
    have hsize := Nat.le_mul_of_pos_left (page E.hosts E.high) (show 0<2*E.dim+2 by omega)
    omega
  refine ⟨⟨?_,?_⟩,fitsOf _ (depth.trans prefix₀) start,fitsOf _ (amount.trans prefix₀) start,
    .inl depth,.inl amount,scanEnd.trans_lt bound,?_,lookup,lanes⟩
  · rw [rows];exact size
  · rw [rows];exact size
  · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (pRoom.trans bound.le)
end Placement

/-- The chart which runs on its paid physical canvas has exactly the dimensions and
precision used by the complete date tariff, including all absent sites and contacts. -/
theorem numbered_estimator (S : AtomSchedule) (k tail i h p f K fullBudget D origin pitch classes floor : ℕ) :
    let m:=S.groupWidth k tail i+k
    let b:=S.localWalshBits p m f K
    let P:=numberedReset S k tail i h p f K fullBudget D origin pitch classes floor
    ∃pos:0<P.geo.bits,
      let E:=P.estimator h (gainBits m f K (S.censusBits p)) pos
      E.dim=m ∧ E.precision=b ∧ E.hosts=S.hostSize i*(m+1+D) ∧ E.payload=h ∧
        E.low=laneBits m h b ∧ E.gainBits≤b := by
  intro m b P
  have l : laneBits m h b≤ m:=Nat.min_le_left ..
  have bits : 0<b:=by dsimp [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits];omega
  refine ⟨bits,?_⟩
  intro E
  have dim : E.dim=m:=by change m-laneBits m h b+laneBits m h b=m;omega
  exact ⟨dim,rfl,by change S.hostSize i*(E.dim+1+D)=_;rw [dim],rfl,rfl,DescentWalshPrecision.gain_le ..⟩

end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
