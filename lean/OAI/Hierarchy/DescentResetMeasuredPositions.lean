import OAI.Hierarchy.DescentRecordedSignedRemix
import OAI.Hierarchy.DescentPaddedFlowRoster

namespace OAI
/-! # The actual depth and first Walsh addresses in the chosen staggered reset directory -/
namespace Hierarchy
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open ThreeFlat.RAM
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
namespace DescentPackedWalsh.EstimatorArena
variable {w base : ℕ} (E : EstimatorArena)

theorem first_below (v : Fin E.hosts) :
    location E.start E.hosts E.high E.dim+(row v (fun _:Fin E.high=>false)).val<E.endAddress := by
  have lt:=(row v (fun _:Fin E.high=>false)).isLt.trans_le (rows_le E.hosts E.high)
  have pow:0<2^E.dim:=Nat.two_pow_pos _
  have num:E.dim+1≤2*E.dim+2:=by omega
  have off:=Nat.mul_le_mul_right (page E.hosts E.high) num
  rw [Nat.add_one_mul] at off
  rw [E.endAddress_eq]
  unfold location
  omega

theorem retained_totals (mem dst : Memory w) (x : Fin E.hosts→Bits E.dim→ℕ) (hi : E.endAddress≤base)
    (same : ∀z<base,dst z=mem z) (old : E.FirstTotals x mem) : E.FirstTotals x dst := by
  intro v
  rw [same _ ((E.first_below v).trans_le hi)]
  exact old v

theorem retained_depth (mem dst : Memory w) (fit : E.Fits w) (hi : E.endAddress≤base)
    (same : ∀z<base,dst z=mem z) (j : ℕ) (index : j<E.hosts) :
    dst (E.depthRows.base+j)=mem (E.depthRows.base+j) := by
  have safe:=Nat.add_lt_add_left (index.trans_le fit.hostRows.1) E.depthRows.base
  have prev:E.start≤E.endAddress:=by rw [E.endAddress_eq];omega
  exact same _ ((safe.trans_le fit.depth.2.2).trans_le (prev.trans hi))
end DescentPackedWalsh.EstimatorArena
namespace DescentSixParty.PackedFlow
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k m H N D : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (name : V≃Fin H) (digits : Block m≃J×Block k)

theorem native_socket (v u : V) (j : Fin A.degree) (selected : portAt A name v j=some u) :
    ∃h:u∈A.mutual v,
      (atPort name A.mutual (fun w=>(Finset.card_filter_le ..).trans (A.degreeBound w)) ⟨v,⟨u,h⟩⟩).2=j := by
  have h:=(actual_ports A name (fun v u h=>(A.symmetric v u).mp h) v u).mpr ⟨j,selected⟩
  let e:Contacts A.mutual:=⟨v,⟨u,h⟩⟩
  let cap : ∀w,(A.mutual w).card≤A.degree:=fun w=>(Finset.card_filter_le ..).trans (A.degreeBound w)
  have one:=atPort_read name A.mutual cap e
  have left:next A name (name v) (atPort name A.mutual cap e).2=some (name u):=by
    rw [next_numbered]
    exact one
  have right:next A name (name v) j=some (name u):=by
    unfold portAt at selected
    cases found:next A name (name v) j with
    | none=>simp [found] at selected
    | some t=>
      simp [found] at selected
      exact congrArg some (name.symm_apply_eq.mp selected)
  exact ⟨h,next_unique A name _ _ left right⟩

theorem physical_port (f : ℕ) (ph : H≤N) (pd : A.degree≤D) (v u : V) (j : Fin A.degree)
    (hit : portAt A name v j=some u) :
    ∃h:u∈A.mutual v,(Canvas.loc (u:=m) (l:=0) A name digits f ph pd
      (.inr (⟨v,⟨u,h⟩⟩:Contacts A.mutual))).val=N*(m+1)+(name v).val*D+j.val := by
  obtain ⟨h,eqn⟩:=native_socket A name v u j hit
  refine ⟨h,?_⟩
  unfold Canvas.loc
  rw [public_port,eqn]
  rfl

end DescentSixParty.PackedFlow
end
end Hierarchy

end OAI
