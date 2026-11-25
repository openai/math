import OAI.Hierarchy.DescentTerminalSortPad
import OAI.Hierarchy.DescentTerminalSortBank

namespace OAI
/-! # Fixed pin wiring for the short sorts of an arbitrary Leighton layer -/

namespace Hierarchy.DescentTerminalHost.SortBank
open Tagged Tagged.SortLift Tagged.TerminalSort ThreeFlat Routing SortNetwork
open scoped Classical BigOperators
noncomputable section

variable {n k w d : ℕ} {V : Type} (S : Stage k) (digit : Fin d→Fin w)
abbrev RowRead (k w : ℕ) (V : Type) := Fin k→Fin w→V ⊕ Bool

def rowValue (v : V→Bool) (row : RowRead k w V) (i : Fin k) (j : Fin w) := Sum.elim v id (row i j)

private def gather (index : (i : Fin S.blocks)→Fin (S.length i)→Fin k) (row : RowRead k w V)
    (i : Fin S.blocks) (j : SortRelation.Data n w) : V ⊕ Bool :=
  let p := (Fintype.equivFin (Payload n w)).symm j
  if good : p.1.val<S.length i then row (index i ⟨p.1.val,good⟩) p.2 else .inr (sentinel digit p.2)

/-- Actual literals fill the unused suffix. All read and write positions
are fixed by the stage's two finite equivalences. -/
def stageRead (old new : RowRead k w V) : BatchRead n w S.blocks V :=
  fun i=>Sum.elim (gather S digit (fun b j=>S.input ⟨b,j⟩) old i)
    (gather S digit (fun b j=>S.output ⟨b,j⟩) new i)

private theorem gather_at (index : (i : Fin S.blocks)→Fin (S.length i)→Fin k)
    (row : RowRead k w V) (v : V→Bool) (i : Fin S.blocks) :
    (fun j=>Sum.elim v id (gather (n:=n) S digit index row i j)) =
    pack (pad (sentinel digit) (fun j=>rowValue v row (index i j)) : Records n w) := by
  funext j
  rcases (Fintype.equivFin (Payload n w)).surjective j with ⟨⟨r,p⟩,rfl⟩
  simp only [gather,pack,Equiv.symm_apply_apply,Function.uncurry_apply_pair,pad]
  split <;> rfl

private theorem input_at (old new : RowRead k w V) (v : V→Bool) (i : Fin S.blocks) :
    inside (stageRead (n:=n) S digit old new) v i =
      pad (sentinel digit) (fun j=>rowValue v old (S.input ⟨i,j⟩)) := by
  change SortedBlock.unwrap (fun j=>Sum.elim v id
    (gather (n:=n) S digit (fun b r=>S.input ⟨b,r⟩) old i j))=_
  rw [gather_at,SortedBlock.unwrap_pack]

private theorem output_at (old new : RowRead k w V) (v : V→Bool) (i : Fin S.blocks) :
    output (stageRead (n:=n) S digit old new) v i =
      pack (pad (sentinel digit) (fun j=>rowValue v new (S.output ⟨i,j⟩)) : Records n w) :=
  gather_at (n:=n) S digit (fun b r=>S.output ⟨b,r⟩) new v i

theorem stage_iff (room : ∀b,S.length b≤2^n) (old new : RowRead k w V) (v : V→Bool) :
    Accepts digit (stageRead (n:=n) S digit old new) v ↔
      rowValue v new=S.eval (key digit) (rowValue v old) := by
  change (∀b,output _ v b = pack (sorted digit (inside _ v b))) ↔ _
  simp_rw [output_at,input_at,sorted_pad digit (room _)]
  constructor
  · intro accepted
    funext i j
    obtain ⟨⟨b,r⟩,rfl⟩:=S.output.surjective i
    have eq := congrArg (SortedBlock.unwrap (l:=n) (w:=w)) (accepted b)
    simp only [SortedBlock.unwrap_pack] at eq
    have read:=congrFun (congrFun eq (Fin.castLE (room b) r)) j
    simpa only [pad,Fin.val_castLE,r.isLt,dite_eq_left,Stage.eval_output,Function.comp_def,Fin.eta] using read
  · intro valid b
    apply congrArg pack
    funext i
    by_cases hi : i.val<S.length b
    · simp [pad,hi,valid,Stage.eval_output,Function.comp_def]
    · simp [pad,hi]

end
end Hierarchy.DescentTerminalHost.SortBank

end OAI
