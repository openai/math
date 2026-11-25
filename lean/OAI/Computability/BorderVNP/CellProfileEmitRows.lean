import OAI.Computability.BorderVNP.CellPrefixEmit
import OAI.Computability.BorderVNP.CellProfileWordEmit
import OAI.Computability.BorderVNP.CellProfileEmitAddress
import OAI.Computability.BorderVNP.CellProfileWeaken
import OAI.Computability.QuantumFactoring.BitStackMultiplier
import OAI.Computability.QuantumFactoring.Procedure

/-! # Private serializers for selector, histogram, and route checks

These procedures build the original compact command descriptors, including the
lexical copy/candidate/lane addresses. Binary copy counts and route widths are
stored as loop bounds in the generated program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

variable {α : Type} {ea : α → List Bool}

/-- Compute the size of all profile flag tables from binary copy and term counts. -/
noncomputable def profileAux {c n : α → ℕ} (hc : Procedure ea Nat.bits c) (hn : Procedure ea Nat.bits n) :
    Procedure ea Nat.bits (fun x => Profile.auxSize (c x) (n x)) :=
  Procedure.binaryMul.comp (hn.pair (Procedure.binaryMul.comp ((prefixSucc hc).pair (prefixSucc hc))))

/-- Compute the physical first slot of the table for one selected term. -/
noncomputable def profileTermBase {base c t : α → ℕ}
    (hb : Procedure ea Nat.bits base) (hc : Procedure ea Nat.bits c) (ht : Procedure ea Nat.bits t) :
    Procedure ea Nat.bits (fun x => Profile.termBase (base x) (c x) (t x)) :=
  Procedure.binaryAdd.comp (hb.pair (profileAux hc ht))

/-- Print the comparison between a dynamically supplied term and all selector bits of one copy. -/
noncomputable def profileSelect {off w t : α → ℕ} {p : α → Port} {i : α → NatExpr}
    (ho : Procedure ea Nat.bits off) (hp : Procedure ea Typed.port p) (hw : Procedure ea unaryCode w)
    (ht : Procedure ea Nat.bits t) (hi : Address ea i) :
    Boolean ea (fun x => Profile.selectTerm (off x) (p x) (w x) (t x) (i x)) := by
  let pull := Procedure.first ea Nat.bits
  exact wordIsRange (a := fun x k => Profile.portExpr (off x) (p x) (i x) (.lit k)) hw ht
    (shiftedPortAddr (ho.comp pull) (hp.comp pull) (preAddr hi pull) (litAddr (Procedure.second ea Nat.bits)))

/-- Serialize the single bounded-loop body checking each copy's selector range. -/
noncomputable def profileRange {off c w n : α → ℕ} {p : α → Port}
    (ho : Procedure ea Nat.bits off) (hc : Procedure ea Nat.bits c) (hp : Procedure ea Typed.port p)
    (hw : Procedure ea unaryCode w) (hn : Procedure ea unaryCode n) :
    Statement ea (fun x => Profile.rangeGen (off x) (c x) (p x) (w x) (n x)) := by
  let pull := Procedure.first ea Nat.bits
  let ht := Procedure.second ea Nat.bits
  let body := profileSelect (ho.comp pull) (hp.comp pull) (hw.comp pull) ht (constAddr (prodCode ea Nat.bits) (.index 0))
  exact loopStmt (litAddr hc) (guardBool (anyRange (t := fun x t => Profile.selectTerm (off x) (p x) (w x) t (.index 0)) hn body))

/-- Generate one term's prefix table and its final advertised-count check, including
the failing branch for an advertised count larger than the number of copies. -/
noncomputable def profileTerm {base off c w t adv : α → ℕ} {p : α → Port}
    (hb : Procedure ea Nat.bits base) (ho : Procedure ea Nat.bits off) (hc : Procedure ea Nat.bits c)
    (hp : Procedure ea Typed.port p) (hw : Procedure ea unaryCode w)
    (ht : Procedure ea Nat.bits t) (hadv : Procedure ea Nat.bits adv) :
    Statement ea (fun x => Profile.termGen (base x) (off x) (c x) (p x) (w x) (t x) (adv x)) := by
  let origin := profileTermBase hb hc ht
  let matched := profileSelect ho hp hw ht (constAddr ea (.index 1))
  have hm : Boolean ea (fun x => (Profile.selectTerm (off x) (p x) (w x) (t x) (.index 0)).weaken) :=
    matched.congrFun (fun x => congrArg (fun a : Term => CellMacro.Generator.serialized 8 (a.emit x.2))
      (Profile.weaken_selectTerm (off x.1) (p x.1) (w x.1) (t x.1) (.index 0)).symm)
  let table := prefixGenerator (m := fun x => Profile.selectTerm (off x) (p x) (w x) (t x)) origin hc hc hm
  let test := Procedure.binaryLe.comp (hadv.pair hc)
  let yes := guardBool (prefixFlag origin hc (litAddr hc) (litAddr hadv))
  let no := constStmt ea (Term.lit false).guard
  let finish := Procedure.conditional test yes no
  apply seqStmt table
  apply finish.congrFun
  intro x
  by_cases h : adv x ≤ c x <;> simp [h]

/-- Emit the triple-loop routing check for one supplied destination, preserving
the rank from the strictly earlier prefix and both original port strides. -/
noncomputable def profileRoute {base off c w n : α → ℕ} {p : α → Port} {r : α → Route}
    (hb : Procedure ea Nat.bits base) (ho : Procedure ea Nat.bits off) (hc : Procedure ea Nat.bits c)
    (hp : Procedure ea Typed.port p) (hw : Procedure ea unaryCode w)
    (hn : Procedure ea Nat.bits n) (hr : Procedure ea Typed.route r) :
    Statement ea (fun x => Profile.routeGen (base x) (off x) (c x) (p x) (w x) (n x) (r x)) := by
  let fields := ProfileData.routeFields.comp hr
  let term := (Procedure.first ..).comp fields
  let rest := (Procedure.second ..).comp fields
  let lanes := (Procedure.first ..).comp rest
  let ports := (Procedure.second ..).comp rest
  let original := (Procedure.first ..).comp ports
  let compact := (Procedure.second ..).comp ports
  let i := constAddr ea (.index 2)
  let k := constAddr ea (.index 1)
  let lane := constAddr ea (.index 0)
  let enabled := andBool (profileSelect ho hp hw term i) (prefixFlag (profileTermBase hb hc term) hc i k)
  let same := equalBool (wireBool (shiftedPortAddr ho original i lane)) (wireBool (shiftedPortAddr ho compact k lane))
  let oneLane := guardBool (orBool (notBool enabled) same)
  let range := guardBool (literalBool (Procedure.binaryLt.comp (term.pair hn)))
  exact seqStmt range (loopStmt (litAddr hc) (loopStmt (litAddr (prefixSucc hc)) (loopStmt (litAddr lanes) oneLane)))

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
