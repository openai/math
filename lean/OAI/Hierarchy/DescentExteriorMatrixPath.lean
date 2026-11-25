import OAI.Hierarchy.DescentExteriorMatrixDates
import OAI.Hierarchy.DescentPathPinSpine

namespace OAI
/-! # The full exterior matrix word computed from prior selected scalar and GL records -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentExteriorMatrixUpdate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k tail wire hist : ℕ} {bits:P→ℕ} {G:PoweredGadget F}
    {S:AtomSchedule} {q ε:ℝ} {I W:MarkedWorld F d P bits} {z₀ D₀ i z D:ℕ}
    {initial:Reached I G q ε S k 0 z₀ D₀ wire hist} {current:Reached W G q ε S k i z D wire hist}
    (base:S.baseGroups=2^tail) (radix:S.radix=2^k) (p:ℕ) (hp:0<p)
    (a:Archive I) (seed:a.Particles initial)
    (path:Path initial current) (r:path.recorded p) {bw:ℕ} (cell:ℕ→Cell) (m:Memory bw)
local notation "dim" => S.groupWidth k tail 0+k

/-- The inputs are the actually selected local matrix word and the literal ROM of this date.
In particular neither the running nor final global matrix is a parameter of the receipt. -/
def Path.matrixInputs : Prop := by
  induction path with
  | here=>exact True
  | @ordinary A age zi Di zn Dn src prev fee he T c norm dst ticket ih =>
    let past:=prev.pinSpine base radix p hp a r seed
    let owns:=(prev.particles p hp a r seed).attached
    let next:=ticket.pinStep base radix owns
    let rot:=multiplier src.placement.fieldBits (BitDescription.scannedRows he src.placement.stage).μ
    let ext:=Spine.promoteCut past.width (past.append next).width (ordinaryCut k (S.group_cut ticket.hubRows.choose))
    exact ih r ∧ (cell age).Room bw dim k ∧ (cell age).Shelf (reached cell m age) ext rot
  | @reset A age zi Di n h C f g cut tail' src prev ctl b ih=>
    have eqTail:tail=tail':=by simpa only [Nat.log2_two_pow] using congrArg Nat.log2 (base.symm.trans ctl.base)
    subst tail'
    let past:=prev.pinSpine base radix p hp a r.1 seed
    let owns:=(prev.particles p hp a r.1 seed).attached
    let next:=b.pinStep owns
    let ext:=Spine.promoteCut past.width (past.append next).width (resetCut k (S.group_cut b.age))
    exact ih r.1 ∧ (cell age).Room bw dim (S.groupWidth k tail age+k) ∧ (cell age).Shelf (reached cell m age) ext b.frame.basis

theorem Path.matrix_read (inputs:path.matrixInputs base radix p hp a seed r cell m)
    (start:m (cell 0).old.base=((matrixCode (Spine.start (active initial base radix) (host initial)).matrix).val:Computability.VPVNP.BurstRAM.Word bw))
    (join:∀t < i,(cell t).updated=(cell (t+1)).old.base) :
    reached cell m i (cell i).old.base=((matrixCode (path.pinSpine base radix p hp a r seed).matrix).val:Computability.VPVNP.BurstRAM.Word bw) := by
  induction path with
  | here=>exact start
  | ordinary prev ticket ih=>
    obtain ⟨past,ok,shelf⟩:=inputs
    have before:=ih r past (fun t ht=>join t (by omega))
    rw [←join _ (Nat.lt_succ_self _)]
    have step:=(cell _).read ok _ _ _ _ before shelf
    rw [←entry_read] at step
    rwa [ticket.matrix_word] at step
  | @reset A age zi Di n h C f g cut tail' src prev ctl b ih=>
    have eqTail:tail=tail':=by simpa only [Nat.log2_two_pow] using congrArg Nat.log2 (base.symm.trans ctl.base)
    subst tail'
    obtain ⟨past,ok,shelf⟩:=inputs
    have before:=ih r.1 past (fun t ht=>join t (by omega))
    rw [←join _ (Nat.lt_succ_self _)]
    have step:=(cell _).read ok _ _ _ _ before shelf
    rw [←entry_read] at step
    rwa [b.matrix_word (prev.particles p hp a r.1 seed).attached] at step

end
end Hierarchy.DescentSixParty.Chronology

end OAI
