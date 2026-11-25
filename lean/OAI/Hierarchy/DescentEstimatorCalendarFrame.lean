import OAI.Hierarchy.DescentPackedWalshResident

namespace OAI
/-! # The estimator depth calendar confines its writes on every memory image -/
namespace Hierarchy.DescentPackedWalshReduction.Plan
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (P : Plan) {w : ℕ}

theorem state_frame (root first n : ℕ) (m : Memory w) (a : ℕ)
    (outside : a<first ∨ P.dataAt first (n+1)≤a) : P.state root first m n a=m a :=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    let now:=P.state root first m n
    have start : first≤P.dataAt first (n+1):=P.data_mono first (Nat.zero_le _)
    have common : a<P.dataAt first (n+1) ∨ P.dataAt first (n+2)≤a :=
      outside.imp_left (fun lo=>lo.trans_le start)
    have step : P.stateStep root first n now a=now a :=by
      by_cases scalar:P.scalar n
      · obtain ⟨_,_,_,k₁⟩:=P.scalar_lanes scalar
        simp only [stateStep,ite_eq_left scalar,DescentWalshScalarReduction.after]
        apply ProtocolRAMGeneratedWrite.frame_image
        simpa only [dataAt,k₁] using common
      · simpa only [stateStep,ite_eq_right scalar] using
          (ProtocolRAMGeneratedWrite.frame_image (P.dataAt first (n+1)) (P.tile n).rows
            ((P.tile n).banks (P.headerAt root n) (P.dataAt first n)).read now a
            (by rw [P.rows];exact common))
    exact step.trans (ih (outside.imp_right (fun h=>(P.data_mono first (by omega : n+1≤n+2)).trans h)))

end
end Hierarchy.DescentPackedWalshReduction.Plan

namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w : ℕ}

theorem Column.frame (P : Plan) (root first extract out : ℕ) (m : Memory w) (a : ℕ)
    (rows : P.dataAt first (P.depth+1)≤out) (outside : a<first ∨ out+2^P.axis≤a) :
    Column.publishMem P root first extract out m a=m a :=by
  have inside : first≤out:=(P.data_mono first (Nat.zero_le _)).trans rows
  have afterOut : out≤out+2^P.axis := Nat.le_add_right ..
  have inner : a<first ∨ P.dataAt first (P.depth+1)≤a :=
    outside.imp_right (fun h=>(rows.trans afterOut).trans h)
  have ghosts : P.ghostBase first+P.ghostRows≤out:=(P.pad_end first).le.trans
    ((P.data_mono first (by omega : 1≤P.depth+1)).trans rows)
  have pin : P.pad first m a=m a:=ProtocolRAMGeneratedWrite.frame_image _ _ _ m a
    (outside.imp (fun h=>h.trans_le (Nat.le_add_right first _)) (fun h=>(ghosts.trans afterOut).trans h))
  exact (ProtocolRAMGeneratedWrite.frame_image out _ _ _ a (outside.imp_left (fun h=>h.trans_le inside))).trans
    ((P.state_frame root first P.depth _ a inner).trans pin)

namespace EstimatorArena
variable (E : EstimatorArena)

theorem calendar_frame (fit : E.Fits w) (m : Memory w) (a : ℕ)
    (outside : a<E.inputEnd ∨ E.solveAt≤a) :
    E.calendar.state E.plan E.hosts m (E.dim+1) a=m a :=by
  have step (n : ℕ) (valid : n≤E.dim+1) : E.calendar.state E.plan E.hosts m n a=m a:=by
    induction n with
    | zero=>rfl
    | succ n ih=>
      let prior:=E.calendar.state E.plan E.hosts m n
      let data:=image (E.scratch n) (E.hosts*2^E.high) (Weight.expr E.weights n) prior
      have low : E.inputEnd≤E.scratch n:=E.calendar.pre n
      have upper:=E.includes_bank n valid
      have middle : E.scratch n+E.hosts*2^E.high≤E.bank n:=Nat.add_le_add_left (E.host_words fit) _
      have pushed : data a=prior a:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a
        (outside.imp (fun h=>h.trans_le low)
          (fun h=>middle.trans ((Nat.le_add_right (E.bank n) (2^E.dim)).trans (upper.trans h))))
      have reduced:=Column.frame E.plan E.reduceAt (E.scratch n) E.orderAt (E.bank n) data a
        (E.packed_before n).le (outside.imp (fun h=>h.trans_le low) (fun h=>upper.trans h))
      exact reduced.trans (pushed.trans (ih (by omega)))
  exact step _ le_rfl

end EstimatorArena
end
end Hierarchy.DescentPackedWalsh

end OAI
