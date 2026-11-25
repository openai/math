import OAI.Hierarchy.DescentDatedOperandCoordinates
import OAI.Hierarchy.DescentOperandFamilyBook

namespace OAI
/-! # Paid scalar key functions for the original ordinary operand coordinates -/
namespace Hierarchy.DescentDatedOperandCoordinates
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section

def keyWidth (C : ℕ) := Nat.clog 2 (C+1)
def digit (C n : ℕ) : Cell (keyWidth C) :=
  if small : n≤C then ⟨n,(Nat.lt_succ_of_le small).trans_le (Nat.le_pow_clog (by decide) _)⟩ else 0

@[simp] theorem digit_zero (C : ℕ) : digit C 0=0 := by
  apply Fin.ext
  simp [digit]
theorem digit_at {C n : ℕ} (small : n≤C) : (digit C n).val=n := by simp [digit,small]

/-- Input order is cause, pointer kind, old path, old block, previous peer and previous first serial. -/
def oldLaw (P B D C a : ℕ) (_ : Fin 1) (v : Fin 6 → Cell a) : Cell (keyWidth (P*(B*(D*C)))) :=
  digit _ (oldName P B D C (v 0).val (v 1).val (v 2).val (v 3).val (v 4).val (v 5).val)

/-- Input order is cause, old actor path, issued old slot, issued peer and issued polarity. -/
def pathLaw (P D a : ℕ) (_ : Fin 1) (v : Fin 5 → Cell a) : Cell (keyWidth (P*(D+1))) :=
  digit _ (previousPath P D (v 0).val (v 1).val (v 2).val (v 3).val (v 4).val)

/-- Input order is cause, kind, W path, reached path, W block, signed slot,
signed polarity, newborn first slot and newborn mouth side. -/
def anchorLaw (P B C a : ℕ) (_ : Fin 1) (v : Fin 9 → Cell a) : Cell (keyWidth (P*(B*(C*3)))) :=
  digit _ (anchorKey P B C (v 0).val (v 1).val (sourcePath (v 0).val (v 2).val (v 3).val)
    (v 4).val (v 5).val (v 6).val (v 7).val (v 8).val)

/-- Input order is cause, original W path, reached path, measured lower
anchor ordinal and measured raw role at the newborn mouth. -/
def rawLaw (P O a : ℕ) (_ : Fin 1) (v : Fin 5 → Cell a) : Cell (keyWidth (P*O)) :=
  digit _ (rawSocket P O (v 0).val (sourcePath (v 0).val (v 1).val (v 2).val) (v 3).val (v 4).val)

def localLaw (P a : ℕ) (_ : Fin 1) (v : Fin 3 → Cell a) : Cell (keyWidth P) :=
  if (v 0).val=1 ∧ (v 1).val=0 then digit P ((v 2).val+1) else 0

theorem old_dead (P B D C a : ℕ) (j : Fin 1) : oldLaw P B D C a j (fun _=>0)=0 :=by simp [oldLaw,oldName]
theorem path_dead (P D a : ℕ) (j : Fin 1) : pathLaw P D a j (fun _=>0)=0 :=by simp [pathLaw,previousPath]
theorem anchor_dead (P B C a : ℕ) (j : Fin 1) : anchorLaw P B C a j (fun _=>0)=0 :=by simp [anchorLaw,anchorKey]
theorem raw_dead (P O a : ℕ) (j : Fin 1) : rawLaw P O a j (fun _=>0)=0 :=by simp [rawLaw,rawSocket,sourcePath]
theorem local_dead (P a : ℕ) (j : Fin 1) : localLaw P a j (fun _=>0)=0 :=by simp [localLaw]

theorem old_port {P B D C a : ℕ} (p : Fin P) (x : Fin B) (peer : Fin D) (first : Fin C)
    (v : Fin 6 → Cell a) (h₀ : (v 0).val=1) (h₁ : (v 1).val=1) (h₂ : (v 2).val=p.val)
    (h₃ : (v 3).val=x.val) (h₄ : (v 4).val=peer.val) (h₅ : (v 5).val=first.val) :
    (oldLaw P B D C a 0 v).val=(finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (peer,first)))).val+1 := by
  simp only [oldLaw,h₀,h₁,h₂,h₃,h₄,h₅,old_name_at]
  exact digit_at (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (peer,first)))).isLt

theorem local_port {P a : ℕ} (p : Fin P) (v : Fin 3 → Cell a)
    (cause : (v 0).val=1) (kind : (v 1).val=0) (path : (v 2).val=p.val) :
    (localLaw P a 0 v).val=p.val+1 := by simp [localLaw,cause,kind,path,digit_at p.isLt]

end
end Hierarchy.DescentDatedOperandCoordinates

end OAI
