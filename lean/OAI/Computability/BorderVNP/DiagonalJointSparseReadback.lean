import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.CellSparseExteriorUnique

/-! # Occupied signed inputs on every joint completion of the same local prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM TeamContraction CompactMachine CellDispatch BorderVNP.Cube ScheduleClock
open TeamContraction.ProcessorSlots CellMacro.Generator

variable {R n w dim box lanes selectors symbols : ℕ}
    (id : TableEntry dim box lanes selectors symbols → ℕ) (U : Fin (R+1) → PinStart SparseExterior.driver n w)

local notation3 (prettyPrint := false) "mac(" u ")" => install SparseExterior.driver n (U u).routines
variable {id U} in
/-- Signed input after expanding the actual sparse row at this global index. -/
noncomputable abbrev SparseSource.logicalAt {u} {p : (U u).Prefix id} (data : SparseSource id U p) (i : ℕ) :=
  SparseExterior.logicalCell (data.arguments.placed i) (data.arguments.extra i) (data.arguments.field i)

variable {id U} in
/-- Packed payload before expansion of the locally received sparse bank. -/
noncomputable abbrev SparseSource.bytesAt {u} {p : (U u).Prefix id} (data : SparseSource id U p) (i : ℕ) :=
  CellSparse.Packet.input (data.logicalAt i).directory (data.arguments.placed i).privateWires (data.arguments.field i).bytes

/-- Replay the actual argument and typed writers for this source all the
way to the local dispatch memory. -/
theorem SparseSource.generated {u} {p : (U u).Prefix id} (data : SparseSource id U p) :
    ∃ A : GeneratedCells SparseExterior.driver n (U u).pub p.2.val.2.2, A.cell=data.logicalAt ∧ A.payload=data.bytesAt := by
  let v := visits id U p
  let cut := SignedPrep.typedParts id (U u).pub mac(u) v
  obtain ⟨rows,read,wire⟩ := typedRows_on_arguments v.arguments cut.1 data.source data.arguments
  obtain ⟨A,ha,hp,_⟩ := signedPrep_generated id (U u).pub (U u).routines SparseExterior.driver n (U u).bank (U u).memory
    (U u).pins p.1 p.2 rows
  exact ⟨A,ha.trans read,hp.trans wire⟩

/-- Any two honest argument receipts at the same reached preparation
agree on every cell executed by its team. -/
theorem SparseSource.same_owned {u} {p : (U u).Prefix id} (d e : SparseSource id U p) (i : ℕ)
    (fit : i<(Frame.ofMemory (U u).pub p.2.val.2.2).count)
    (mine : readings p.2.val.2.2 ((Frame.ofMemory (U u).pub p.2.val.2.2).address i)=
      (Frame.ofMemory (U u).pub p.2.val.2.2).team) : d.logicalAt i=e.logicalAt i := by
  obtain ⟨A,ha,hp⟩ := d.generated id U
  obtain ⟨B,hb,hq⟩ := e.generated id U
  have eq := SparseExterior.owned_input_unique A B i fit mine (congrFun hp i) (congrFun hq i)
    (congrFun ha i) (congrFun hb i)
  exact (congrFun ha i).symm.trans (eq.trans (congrFun hb i))

variable (used : Fin (R+1) → ℕ) (c : PhaseCharges)

/-- One continuation implements the reached sparse cell on *every* joint
input, even though the scalar clock certificate for each local prefix was
obtained with one chosen completion on the other teams. -/
theorem joint_sparse_continuation_on_inputs (ok : jointSupport id U) {limit : ℕ}
    (paid : c.core+c.before+c.argumentsCalls+c.finish+c.reader ≤ limit)
    (measured : JointClock id U used c) (source : ∀ a : JointPrefix id U, ∀ u, SparseSource id U (a u))
    (u : Fin (R+1)) :
    ∃ C : PositiveContinuation id SparseExterior.driver n (U u).pub (U u).routines (U u).bank (U u).memory
      (U u).pins (used u) limit, ∀ a : JointPrefix id U, let f := Frame.ofMemory (U u).pub (a u).2.val.2.2
        ∀ i < f.count, readings (a u).2.val.2.2 (f.address i)=f.team →
          (C.cells (a u).1 (a u).2).cell i= (source a u).logicalAt i := by
  obtain ⟨C,read⟩ := joint_sparse_continuation id U used c ok paid measured source u
  refine ⟨C,?_⟩
  intro a f i hi here
  let d := onLocal id U ok source (a u)
  have native := congrFun (read (a u).1 (a u).2).1 i
  exact native.trans (SparseSource.same_owned id U d (source a u) i hi here)

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
