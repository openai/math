import OAI.Hierarchy.DescentPhysicalResetBooks
import OAI.Hierarchy.DescentPhysicalResetPrimeFrame

namespace OAI
/-! # The fixed reset through the paid and installed root programs on every word tape -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSIMDLookup DescentGLPacked DescentPlainTerminal.Suffix DescentSixParty DescentFallbackPeriod
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ)
local notation "P" => a.stencilPhase sh floor count hub g Y
local notation "E" => a.estimator floor

private theorem middle_order : (P).origin≤(P).first ∧ (P).first≤(P).base ∧ (P).base≤(P).endAddress := by
  have span:(P).origin≤(P).fresh:=((a.chart floor).estimator_range a.payload a.gain a.positive).2.2
  refine ⟨?_,?_,?_⟩
  · unfold PackedFlow.ResetMiddle.first PackedFlow.ResetMiddle.saved;omega
  · unfold PackedFlow.ResetMiddle.base Subwords.finish Subwords.destination;omega
  · rw [PackedFlow.ResetMiddle.endAddress,(P).S.extent]
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _

theorem throughStencil_any_framed (src : Bank) (R δ w : ℕ) (m : Memory w)
    (front : a.PrimeRoom floor src count R δ w) (middle : (P).Room w) :
    ∃dst,(a.throughStencil sh floor count hub g Y src R δ w).Exec m dst
        (a.throughStencilTicks sh floor count hub g Y R δ w) ∧
      CheapCode (a.throughStencil sh floor count hub g Y src R δ w) ∧
      ∀i,i<floor ∨ (P).endAddress≤ i→dst i=m i := by
  obtain ⟨prior,pre,kept⟩:=a.prime_any_framed floor src count R δ w m front
  have bounds:=a.middle_order sh floor count hub g Y
  have ordered:(P).chart.heap (P).dim+(P).stages*(P).chart.page≤(P).fresh:=by
    change _≤(P).chart.heap (P).dim+((P).stages+1)*(P).chart.page
    rw [Nat.succ_mul]
    omega
  obtain ⟨dst,go,c,frame⟩:=(P).any_framed middle ((E).image ((E).literal prior)) ordered bounds.1
  have low : floor≤(P).origin:=((a.occupied floor).1.trans ((a.chart floor).estimator_range _ _ a.positive).1).trans
    ((a.chart floor).estimator_range _ _ a.positive).2.1
  have up:(E).endAddress≤(P).endAddress:=bounds.1.trans (bounds.2.1.trans bounds.2.2)
  let frontProgram := a.prime floor src count R δ w
  let backProgram := (P).code w
  let mid := (E).image ((E).literal prior)
  refine ⟨dst,@Procedure.Exec.then w frontProgram backProgram m mid dst
    (a.primeTicks floor R δ w) ((P).time w) @pre @go,?_,?_⟩
  · obtain ⟨frontCheap, _⟩ := a.prime_hardware floor src count R δ w
    exact @cheap_seq w frontProgram backProgram @frontCheap @c
  · intro i outside
    exact (frame i (outside.imp_left (·.trans_le low))).trans (kept i (outside.imp_right (up.trans ·)))

variable (inputs : a.RootInputs)
local notation "v₀" => a.successor.middle
local notation:max "Q" w:arg => a.rootPhase sh floor count hub g Y inputs w
theorem throughPublishedRoots_any_framed
    (book : Projected.RootBook a.successor.middle.rotorBits a.successor.middle.rootDepth a.ports (2^a.successor.middle.rootDepth) (a.c/2) inputs.field)
    (src : Bank) (R δ w : ℕ) (safe : (Q w).PreparedFits book) (m : Memory w)
    (front : a.PrimeRoom floor src count R δ w) (middle : (P).Room w) :
    ∃dst,(a.throughPublishedRoots sh floor count hub g Y inputs book src R δ w safe).Exec m dst
        (a.throughPublishedTicks sh floor count hub g Y inputs book R δ w safe) ∧
      CheapCode (a.throughPublishedRoots sh floor count hub g Y inputs book src R δ w safe) ∧
      ∀i,i<floor ∨ (Q w).preparedEnd book≤ i→dst i=m i := by
  obtain ⟨measured,run,c,frm⟩:=a.throughStencil_any_framed sh floor count hub g Y src R δ w m front middle
  obtain ⟨root,cheap,held⟩:=(Q w).prepared_any book safe measured
  have phases:=a.middle_order sh floor count hub g Y
  have low : floor≤(P).origin:=((a.occupied floor).1.trans ((a.chart floor).estimator_range _ _ a.positive).1).trans
    ((a.chart floor).estimator_range _ _ a.positive).2.1
  have h:=book.limits (Q w).projectionEnd (v₀).signedHosts (2^(v₀).stencil.c) (v₀).signedLanes
  have loaded:(Q w).projectionEnd≤(Q w).headerEnd book:=h.1.trans (h.2.1.trans h.2.2)
  have end_:(P).endAddress≤(Q w).preparedEnd book:=((Q w).origin_le_projection.trans loaded).trans (Nat.le_add_right ..)
  have floorRoot:floor≤(Q w).origin:=low.trans (phases.1.trans (phases.2.1.trans phases.2.2))
  let head := a.throughStencil sh floor count hub g Y src R δ w
  let tail := (Q w).preparedRoots book safe
  let dst := (Q w).preparedImage book safe measured
  refine ⟨dst,@Procedure.Exec.then w head tail m measured dst
    (a.throughStencilTicks sh floor count hub g Y R δ w) ((Q w).preparedTicks book safe) @run @root,
    @cheap_seq w head tail @c @cheap,?_⟩
  intro i outside
  exact (held i (outside.imp_left (·.trans_le floorRoot))).trans (frm i (outside.imp_right (end_.trans ·)))
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
