import OAI.Hierarchy.ProtocolRAMPurchaseNative

namespace OAI
/-! # Linear charged time for one complete subdivision and sampler purchase -/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open ProbeStage ProbeStage.Native
variable {z d k : ℕ}

/-- The physical table and greedy interpreter bounds with every affine term retained. -/
def costEnvelope (d D h k n : ℕ) :=
  let R := n*D^h
  let H := h+1
  let G := R*(4*H+3)
  subdivisionConstant d*n + (
    (15+6*(4^(rounds d+1)*n)+70*n + (4+H*(4+R*(2*PurchaseColumns.fieldBudget D h+4))) +
      (4+(n+1)*(2*(10+15*(2*k))+4))) +
    (16+3*G*64 + ((4+(4+(n+1)+R)*42)+(3+17*G))))

private theorem affine (d D h k n : ℕ) (pos : 0<n) :
    costEnvelope d D h k n ≤ costEnvelope d D h k 1*n := by
  cases n with
  | zero => omega
  | succ n => unfold costEnvelope; dsimp; ring_nf; omega

/-- Constants depend only on the prescribed geometric and price dimensions.
The layout uses first=0 because the output for this stratum has its own bank. -/
theorem clock_linear (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k)
    (hd : 1≤d) (fresh : c.first=0) : ticks S t c ≤ costEnvelope d S.degree c.depth k 1*2^z := by
  let s := embedded S t c
  let b := sign S t c
  let n := 2^z
  let R := n*S.degree^c.depth
  let L := PurchaseStage.layout s b n c.depth
  have area : Fintype.card (stageAt z d t).Group*(stageAt z d t).span≤4^(rounds d+1)*n :=
    (template_dyadic hd _ (List.get_mem ..)).2
  have paths := PurchaseColumns.clock_bound s.directory s.source.base n c.depth (PurchaseTape.edge s)
    (fun i => by simp [PurchaseTape.edge,ProtocolRAMPurchaseOwners.nextWord_work,Expr.work])
  have gates := PurchaseStage.dispatchClock_le L
  have initWork : (MarkTape.loadTerm (n+1) L.marks).work=19 := rfl
  have deg : (geom S t c).degree=S.degree := rfl
  have geo : L.first=0 := fresh
  have tile : L.tiles=n+1 := rfl
  have rows : L.candidates=R := by simp [L,PurchaseStage.layout,R,PurchaseTape.count,deg]
  have depth : L.depth=c.depth+1 := rfl
  simp only [geo,tile,rows,depth,MarkTape.loadClock,initWork,Nat.add_zero] at gates
  have footprint := Nat.mul_le_mul_left 6 area
  calc
    ticks S t c ≤ costEnvelope d S.degree c.depth k n := by
      change subdivisionConstant d*n+
        ((15+6*(Fintype.card (stageAt z d t).Group*(stageAt z d t).span)+70*n+
            clock (PurchaseColumns.passes s.directory s.source.base n c.depth (PurchaseTape.edge s))+
            (4+(n+1)*(2*(10+15*(2*k))+4)))+PurchaseStage.dispatchClock L)≤_
      change clock (PurchaseColumns.passes s.directory s.source.base n c.depth (PurchaseTape.edge s))≤
        4+(c.depth+1)*(4+R*(2*PurchaseColumns.fieldBudget S.degree c.depth+4)) at paths
      change _≤ subdivisionConstant d*n+
        ((15+6*(4^(rounds d+1)*n)+70*n+(4+(c.depth+1)*(4+R*(2*PurchaseColumns.fieldBudget S.degree c.depth+4)))+
          (4+(n+1)*(2*(10+15*(2*k))+4)))+
          (16+3*(R*(4*(c.depth+1)+3))*64+((4+(4+(n+1)+R)*42)+(3+17*(R*(4*(c.depth+1)+3))))))
      omega
    _ ≤ _ := affine d S.degree c.depth k n (Nat.two_pow_pos z)

end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
