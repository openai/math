import OAI.Hierarchy.DescentTerminalGrainPrefix
import OAI.Hierarchy.DescentTerminalBoundaryBasis

namespace OAI
/-! # The native cable and exterior counters give the true scalar argument slot -/
namespace Hierarchy.DescentTerminalPointerDigits
open Computability.BorderVNP.Crossing DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentBundleHistory DescentTerminalBoundaryBasis DescentCompiler DescentColonies
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i p : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V k↪ℕ) (v : W.graph.Site) (coords : Function.Injective (fun s=>(A.pos s,A.block s)))
    (port : Attached W.graph v↪ℕ) (hp : 0 < p) (scale : ℕ) (whole : A.z*G.b=scale*p)
local notation "signed" => Stage.signedPanel A native S ready names (Stage.home A v)
local notation "rk" => rank A native S ready names v port
local notation "num" => address W.graph hp rk
local notation "count" => A.grainCount
local notation "size" => fun d : Boundary W.graph v=>poolBatchCount (boundaryWidth W.graph v d) p

include ready hp whole in
omit [Fintype P] in
theorem repetitions (e : W.graph.Edge) : poolBatchCount (W.graph.width e) p=count e*scale := by
  have eqn : W.graph.width e=(count e*scale)*p:=by rw [A.grainCount_fit S ready e,whole,Nat.mul_assoc]
  have fit : p∣W.graph.width e:=⟨count e*scale,eqn.trans (Nat.mul_comm ..)⟩
  have batches:=DescentTerminalGraphVolume.exact_pieces p (W.graph.width e) hp fit
  exact (Nat.mul_left_inj (Nat.ne_of_gt hp)).mp (batches.trans eqn)

include coords whole in
theorem cable_digit (q₀ psize : ℕ) (used : Finset ℕ) (e : Incident W.graph v) (j : ℕ)
    (clip : (j+1)*p≤W.graph.width e.val) (peer serial : ℕ)
    (located : rk (.inl e)=peer*A.cap+serial) :
    convert q₀ A.cap scale psize (grains signed) used (.cable peer serial j)=
      (num (⟨.inl e,j,clip⟩ : SiteRef (p:=p) W.graph v)).val+1 := by
  have alive : 0 < count e.val := by
    by_contra! no
    have eqn:=A.grainCount_fit S ready e.val
    rw [show count e.val=0 by omega,Nat.zero_mul] at eqn
    have nonempty : 0 < W.graph.width e.val :=
      (Nat.mul_pos (Nat.zero_lt_succ j) hp).trans_le clip
    exact (Nat.ne_of_gt nonempty) eqn
  have top : rk (.inl e) < A.degree*A.cap := by
    rw [positive_rank _ _ _ _ _ _ port e alive]
    exact (label A native S ready names v e alive).isLt
  change lower (grains signed) (peer*A.cap+serial)*scale+j+1=_
  rw [←located,lower_grains A native S ready names v coords _ port,address_val]
  change _=((ProtocolRAMPortRanks.«prefix» size rk (.inl e))+j)+1
  unfold ProtocolRAMPortRanks.«prefix»
  rw [Finset.sum_filter,Fintype.sum_sum_type,Finset.sum_mul]
  have skip : (∑t : Attached W.graph v,if rk (.inr t) < rk (.inl e) then size (.inr t) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro t _
    have le : A.degree*A.cap≤rk (.inr t):=by rw [pin_rank];omega
    simp [show ¬rk (.inr t) < rk (.inl e) by omega]
  rw [skip,Nat.add_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro f _
  by_cases smaller : rk (.inl f) < rk (.inl e) <;>
    simp only [smaller,ite_true,ite_false,Nat.zero_mul]
  exact (repetitions A S ready hp scale whole f.val).symm

include coords whole in
theorem exterior_digit (q₀ psize : ℕ) (used : Finset ℕ) (pin : Attached W.graph v) (ordinal j : ℕ)
    (dense : (Finset.univ.filter (fun u : Attached W.graph v=>port u < port pin)).card=ordinal)
    (common : ∀t : Attached W.graph v,poolBatchCount (bits t.val) p=psize)
    (clip : (j+1)*p≤bits pin.val) :
    convert q₀ A.cap scale psize (grains signed) used (.pin ordinal j)=
      (num (⟨.inr pin,j,clip⟩ : SiteRef (p:=p) W.graph v)).val+1 := by
  change (grains signed).card*scale+ordinal*psize+j+1=_
  rw [all_grains A native S ready names v coords,address_val]
  change _=(ProtocolRAMPortRanks.«prefix» size rk (.inr pin)+j)+1
  unfold ProtocolRAMPortRanks.«prefix»
  rw [Finset.sum_filter,Fintype.sum_sum_type,Finset.sum_mul]
  have cables e : (if rk (.inl e) < rk (.inr pin) then size (.inl e) else 0)=count e.val*scale := by
    change (if _ then poolBatchCount (W.graph.width e.val) p else 0)=_
    rw [repetitions A S ready hp scale whole]
    by_cases pos : 0 < count e.val
    · have bounded:=(label A native S ready names v e pos).isLt
      rw [positive_rank _ _ _ _ _ _ port e pos,pin_rank]
      simp [show (label A native S ready names v e pos).val < A.degree*A.cap+2*port pin+1 by omega]
    · simp [show count e.val=0 by omega]
  have pins (t : Attached W.graph v) : (if rk (.inr t) < rk (.inr pin) then size (.inr t) else 0)=
      if port t < port pin then psize else 0 := by
    have cond : rk (.inr t) < rk (.inr pin) ↔ port t < port pin:=by rw [pin_rank,pin_rank];omega
    change (if _ then poolBatchCount (bits t.val) p else 0)=_
    simp only [cond,common]
  simp only [cables,pins,←Finset.sum_filter,Finset.sum_const,smul_eq_mul,dense]
end
end Hierarchy.DescentTerminalPointerDigits

end OAI
