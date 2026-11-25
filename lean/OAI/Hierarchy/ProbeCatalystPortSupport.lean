import OAI.Hierarchy.ProbeCatalystArchiveRows

namespace OAI
/-! # The decoded physical catalyst role of a positive signed occurrence -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires
open scoped Classical

/-- A positive debit identifies one of the named roles at its original
row-major position on the padded board. -/
def PositivePorts {T C : Type*} [Fintype T] {k count payload : ℕ}
    (tag : C→Fin k→T) (rows stride : ℕ) (record : Entry count payload) : Prop :=
  ∀i,0<record.bits i→∃ (row : Fin rows) (c : C) (axis : Fin k),
    i.val=(Fintype.equivFin T (tag c axis)).val+stride*row.val


variable {R C H E G : Type*} [Fintype C] [Fintype H] [Fintype E] {k balls D count payload : ℕ}

theorem repair_positive_ports (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D)
    (columns : R×C ↪ G) (keys : G×Fin k ↪ Fin count) (idle : Fin count)
    (read : Fin balls×Fin D→ℕ) (fit : ∀v,read (portCell ballsAt bound v)≤payload) :
    PositivePorts (fun c j=>(.catalyst c j : Role C H E k)) balls D
      (repairEntry ballsAt bound columns keys idle read fit) := by
  intro i positive
  let cell := finProdFinEquiv.symm (show Fin (balls*D) from i)
  change 0<(decode ballsAt bound cell).elim 0 (fun _=>read cell) at positive
  cases found : decode ballsAt bound cell with
  | none => simp only [found,Option.elim_none,Nat.lt_irrefl] at positive
  | some src =>
    have idx := (congrArg finProdFinEquiv (decode_spec ballsAt bound found)).trans
      (finProdFinEquiv.apply_symm_apply i)
    exact ⟨ballsAt src.1,src.2.1,src.2.2,congrArg Fin.val idx.symm⟩

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
