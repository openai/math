import OAI.Hierarchy.DescentOrdinaryDonorRows
import OAI.Hierarchy.DescentHaloCompilation
import OAI.Hierarchy.DescentHaloRebaseRAM
import OAI.Hierarchy.DescentPackedOperandOrigins

namespace OAI
/-! # The inherited parent ticket from its physical eleven-role address -/
namespace Hierarchy.DescentOrdinaryIssuedTicket
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentHaloWalkRAM DescentHostDirectory DescentOrdinaryDonorHalo DescentCableDonorNames
open DescentSixParty DescentSharedCableNames DescentRawCablePanel DescentCompiler Computability.BorderVNP.Crossing
open ThreeFlat.RAM PhysicalProcedure
open DescentPackedOperand.Origins (column)
open scoped Classical Fin.CommRing
noncomputable section

/-- The high old group digit selects the hardware lane and is absent from the
new local name. Only the block, first-grain slot and eleven-way role remain. -/
def within {groups k cap : ℕ} (i : Fin (span groups k cap)) : Fin (2^k*cap*11) :=
  let a : Fin (groups*2^k*cap) × Fin 11:=finProdFinEquiv.symm i
  let b : Fin (groups*2^k) × Fin cap:=finProdFinEquiv.symm a.1
  let t : Fin groups × Fin (2^k):=finProdFinEquiv.symm b.1
  finProdFinEquiv (finProdFinEquiv (t.2,b.2),a.2)

section
variable {I J V F P U : Type} [Fintype I] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Field F]
  {H D groups k i d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
    (old : W.graph.Edge↪ℕ) (name : V↪Fin H) (group : J≃Fin groups) (pick : I×Fin 2↪W.graph.Edge)
    (e : Live A pick)
local notation "prior" => W.graph.src (anchor pick e.val)
local notation "outgoing" => Stage.outgoing A old S ready (Subtype.mk (anchor pick e.val) e.property)
local notation "issued" => slot A S ready old name group pick

omit [Fintype I] in
theorem within_read : (within (issued e).2).val=(((A.block prior).val*A.cap+(outgoing).val)*11+(role e.val).val) := by
  change (within (groups:=groups) (k:=k) (cap:=A.cap) (finProdFinEquiv
    (finProdFinEquiv (finProdFinEquiv (group (A.pos prior).1,A.block prior),outgoing),role e.val))).val=_
  simp only [within,Equiv.symm_apply_apply,finProdFinEquiv_apply_val]
  ring

variable (R : Fin H→Fin D→Option (Fin H))
    (listed : ∀v u,u∈A.near v→∃j,R (name v) j=some (name u))
    (reciprocal : ∀v u j,R v j=some u→∃l,R u l=some v)
    (key : U→Key (J×V)) (src : U) (pathTo : Fin (breadth D))
local notation "halo" => DescentHaloCompilation.atSource A.near name R listed A.pos A.block ready.coordinates key
local notation "fromRack" => name (Prod.snd (A.pos prior))
local notation "toRack" => name (Prod.snd (Prod.fst (key src)))

include reciprocal

omit [Fintype I] in
/-- The numerical reverse rank is looked up at the donor itself on the path to
the new source. Consequently both orientations reconstruct the same ticket. -/
theorem from_path (member : prior∈(halo).member src)
    (hit : walk R fromRack (path pathTo) 4=some toRack) :
    Rebase.value R .rank fromRack pathTo*(2^k*A.cap*11)+(within (issued e).2).val=
      (DescentCableDonorNames.code (⟨(halo).slot src ⟨prior,member⟩,outgoing,role e.val,0⟩ :
        Ticket (breadth D*2^k) A.cap 1)).val := by
  obtain ⟨j,_,_,read⟩:=Rebase.actual R reciprocal fromRack toRack pathTo hit
  have slotVal : ((halo).slot src ⟨prior,member⟩).val=
      Ranks.earlier (Rebase.terminal R) toRack (fromRack).val*2^k+(A.block prior).val := by
    change (finProdFinEquiv (DescentHaloDonorChart.rank R toRack fromRack _,A.block prior)).val=_
    have endpoints : Rebase.terminal R=DescentHaloDonorChart.endpoint R := rfl
    simp [finProdFinEquiv_apply_val,DescentHaloDonorChart.rank,endpoints,Nat.mul_comm,Nat.add_comm]
  rw [read,within_read,DescentCableDonorNames.code_val]
  dsimp only
  rw [slotVal]
  simp only [Fin.val_zero,Nat.add_zero,Nat.mul_one]
  ring

end

/-- One packed binary lookup rebases all active lanes. The low ordinal is
the previous fixed within-group column, recoverable even on partial batches. -/
def numeral {a b : ℕ} (radix outBits : ℕ) (reverse : Cell a) (low : Cell b) : Cell outBits :=
  (reverse.val*radix+low.val : ℕ)

set_option maxHeartbeats 900000 in
theorem execute {a b H r M w : ℕ} (radix outBits : ℕ) (T : Tables) (reverse low : Bank) (out : ℕ)
    (fit : DescentPackedZip.Fits T (column reverse) (column low) a b M out w)
    (space : out+H*chunks r M<2^w) (v : Fin H→Fin r→Cell a) (j : Fin H→Fin r→Cell b) :
    (DescentPackedOperand.Origins.program T reverse low out H r M w).Spec
      (fun m=>Static T (numeral (a:=a) (b:=b) radix outBits) M m ∧
        Source (column reverse) v M m ∧ Source (column low) j M m)
      (fun _ m=>∀p : Row H r M,m (out+(row H r M p).val)=((data (fun h g=>numeral radix outBits (v h g) (j h g)) p).val:ℕ))
      (4+54*(H*chunks r M)) ∧ CheapCode (DescentPackedOperand.Origins.program T reverse low out H r M w) := by
  obtain ⟨step,cheap⟩:=DescentPackedZip.spec T (column reverse) (column low) out fit space
    (numeral radix outBits) (by simp [numeral]) v j
  refine ⟨step.mono (fun _ h=>h) (fun _ _ h=>h.2) ?_,cheap⟩
  change 4+H*chunks r M*(2*25+4)≤_
  omega

end
end Hierarchy.DescentOrdinaryIssuedTicket

end OAI
