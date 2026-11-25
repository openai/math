import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentDensePrivateAliases
import OAI.Hierarchy.DescentSharedCableNames

namespace OAI
/-! # Resolving reached short pointers to scalar argument numbers -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentOperandStateBanks DescentKernelHistory DescentSharedCableNames DescentTerminalChronologicalBooks
open DescentLocalPrivateNames
open scoped Classical BigOperators
noncomputable section
variable {D cap L : ℕ}

/-- Both signed appearances of a loop describe the same measured grain. -/
def grain (u : Stage.Live D cap) : ℕ×ℕ :=
  (u.neighbor.val*cap+(u.wire.val-u.within.val),u.within.val)

def present {A : Type} [DecidableEq A] (x : Fin L→ Option A) : Finset A :=
  Finset.univ.biUnion (fun j=>(x j).toFinset)

theorem on_panel {A : Type} [DecidableEq A] (x : Fin L→ Option A) (a : A) :
    a∈present x ↔ ∃i,x i=some a := by simp [present]

def grains (x : Fin L→ Option (Stage.Live D cap)) := present (fun j=>(x j).map grain)
def lower (board : Finset (ℕ×ℕ)) (stop : ℕ) := (board.filter (fun v=>v.1 < stop)).card
def earlier (used : Finset ℕ) (name : ℕ) := (used.filter (·<name)).card

/-- Public pin numbers are the position in the sorted cohort of the current common host. -/
def convert (q cap edgeWords pinWords : ℕ) (board : Finset (ℕ×ℕ)) (used : Finset ℕ) : Pointer→ℕ
  | .privateWord label=>q+earlier used label+1
  | .cable peer first chunk=>lower board (peer*cap+first)*edgeWords+chunk+1
  | .pin pin chunk=>board.card*edgeWords+pin*pinWords+chunk+1

section Private
variable {A T : Type} (r : Recipe T A) {K : ℕ} (slot : Slot r↪Fin K)

def privateName (s : Slot r) : Option ℕ :=
  match h:r.operand s.1 s.2 with
  | .inl _=>none
  | .inr w=>some (firstAlias r slot ⟨w,⟨s.1,s.2,h⟩⟩).val

theorem private_image (whereAt : Slot r↪Fin L) (a : Fin L→ Option ℕ) (hit : ∀s,a (whereAt s)=privateName r slot s)
    (empty : ∀i,(∀s,whereAt s≠i)→ a i=none) :
    present a=Finset.univ.map ((firstAlias r slot).trans Fin.valEmbedding) := by
  ext j
  rw [on_panel,Finset.mem_map]
  constructor
  · rintro ⟨i,found⟩
    by_cases covered : ∃s,whereAt s=i
    · obtain ⟨s,rfl⟩:=covered
      rw [hit,privateName] at found
      split at found
      · contradiction
      · rename_i w hw
        exact ⟨⟨w,⟨s.1,s.2,hw⟩⟩,Finset.mem_univ _,Option.some.inj found⟩
    · rw [empty i (not_exists.mp covered)] at found;contradiction
  · rintro ⟨u,_,rfl⟩
    obtain ⟨n,j,atWord⟩:=u.property
    refine ⟨whereAt ⟨n,j⟩,?_⟩
    rw [hit,privateName]
    split
    · rename_i v hv
      cases hv.symm.trans atWord
    · rename_i w hw
      have same : w=u.val := Sum.inr.inj (hw.symm.trans atWord)
      subst w
      rfl

theorem private_digit (whereAt : Slot r↪Fin L) (a : Fin L→ Option ℕ) (hit : ∀s,a (whereAt s)=privateName r slot s)
    (empty : ∀i,(∀s,whereAt s≠i)→ a i=none) (q cap edgeWords pinWords : ℕ) (board : Finset (ℕ×ℕ)) (h : r.UsedWord) :
    convert q cap edgeWords pinWords board (present a) (.privateWord (firstAlias r slot h).val)=
      q+(ordinal ((firstAlias r slot).trans Fin.valEmbedding) h).val+1 := by
  rw [private_image r slot whereAt a hit empty,ordinal_val]
  simp only [convert,earlier,Finset.filter_map,Finset.card_map]; rfl
end Private

end
end Hierarchy.DescentTerminalPointerDigits

end OAI
