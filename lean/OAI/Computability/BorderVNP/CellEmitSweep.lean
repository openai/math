import OAI.Computability.BorderVNP.CellEmitBoxCounts
import OAI.Computability.BorderVNP.CellFactorEmit

/-! # Native construction of repeated-site scan templates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- A physical per-factor printer, with both the enclosing and the weakened
addresses available. The weakened addresses are used by a prefix-table body
under its one additional lexical counter. -/
abbrev Body {α : Type} (ea : α → List Bool) (body : α → FactorBody) :=
  ∀ {β : Type} (eb : β → List Bool) {source : β → α} {f : β → Factor} {j off i : β → NatExpr},
    Procedure eb ea source → Procedure eb Typed.factor f → Address eb j → Address eb off →
    Address eb i → Address eb (fun x => (j x).weaken) → Address eb (fun x => (off x).weaken) →
    Statement eb (fun x => body (source x) (f x) (j x) (off x) (i x))

private theorem sweep_eq_sequence (body : FactorBody) (bs : List BoxBlock) (start : ℕ) :
    sweep body bs start = sequence (bs.mapIdx (fun i b => b.fragment
      (start + ((bs.take i).map fun z => z.copies*z.factors.length).sum) body)) := by
  induction bs generalizing start with
  | nil => rfl
  | cons b bs ih =>
    rw [sweep, List.mapIdx_cons, ih]
    simp [sequence, Nat.add_assoc]

/-- Compile one sparse block by printing a single parameterized template per
stored private factor. Copy multiplicity is a binary loop bound. -/
noncomputable def fragmentStmt {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {body : α → FactorBody} {src : β → α} {blk : β → BoxBlock} {start : β → ℕ}
    (origin : Procedure eb ea src) (box : Procedure eb blockCode blk) (hs : Procedure eb Nat.bits start)
    (emit : Body ea body) : Statement eb (fun x => (blk x).fragment (start x) (body (src x))) := by
  let factors := blockFactors.comp box
  let nf := (Procedure.listLength Typed.factor (.truth [] [])).comp factors
  let base := blockBase.comp box
  let stride := blockStride.comp box
  let copies := blockCopies.comp box
  let R := prodCode eb (prodCode Nat.bits Typed.factor)
  let owner := Procedure.first eb (prodCode Nat.bits Typed.factor)
  let fj := Procedure.second eb (prodCode Nat.bits Typed.factor)
  let ord := (Procedure.first Nat.bits Typed.factor).comp fj
  let fac := (Procedure.second Nat.bits Typed.factor).comp fj
  let ix := constAddr R (.index 0)
  let wk := constAddr R (.index 1)
  let lo := litAddr (base.comp owner)
  let strideAddr := litAddr (stride.comp owner)
  let firstRow := litAddr (hs.comp owner)
  let factorCount := litAddr (nf.comp owner)
  let ordinal := litAddr ord
  let step := emit R (origin.comp owner) fac
    (addAddr (addAddr firstRow (mulAddr ix factorCount)) ordinal)
    (addAddr lo (mulAddr ix strideAddr)) ix
    (addAddr (addAddr firstRow (mulAddr wk factorCount)) ordinal)
    (addAddr lo (mulAddr wk strideAddr))
  exact loopStmt (litAddr copies) (sequenceMapIdx (f := fun x j f => body (src x) f
    (.add (.add (.lit (start x)) (.mul (.index 0) (.lit (blk x).factors.length))) (.lit j))
    (.add (.lit (blk x).base) (.mul (.index 0) (.lit (blk x).stride))) (.index 0)) (.truth [] []) factors step)

/-- Real fixed stack code that serializes all compact box blocks in directory
order. Each starting ordinal is computed from the sizes of the preceding
blocks, with no advice about the current scan position. -/
noncomputable def sweepStmt {α : Type} {ea : α → List Bool} {dir : α → Directory} {body : α → FactorBody}
    (hd : Procedure ea Typed.directory dir) (emit : Body ea body) :
    Statement ea (fun x => sweep (body x) (dir x).blocks 0) := by
  let src := Procedure.first ea (prodCode Nat.bits blockCode)
  let bj := Procedure.second ea (prodCode Nat.bits blockCode)
  let j := (Procedure.first Nat.bits blockCode).comp bj
  let b := (Procedure.second Nat.bits blockCode).comp bj
  let start := getBlockStart.comp ((hd.comp src).pair j)
  let out := sequenceMapIdx (f := fun (x : α) i (block : BoxBlock) =>
    block.fragment ((((dir x).blocks.take i).map (fun z : BoxBlock => z.copies*z.factors.length)).sum) (body x))
    (⟨0,0,0,[]⟩ : BoxBlock) (getBlocks.comp hd) (fragmentStmt src b start emit)
  exact out.congrFun (fun x => by
    simp only []
    rw [sweep_eq_sequence,List.mapIdx_eq_zipIdx_map]
    simp)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
