import OAI.Hierarchy.DescentOrdinaryPaletteProfile
import OAI.Hierarchy.DescentOrdinaryPaletteBirthLayout
import OAI.Hierarchy.DescentOrdinaryBornChip
import OAI.Hierarchy.DescentPrimitivePaletteToken

namespace OAI
/-! # The original coefficient word of an ordinary six-party birth -/
namespace Hierarchy.DescentOrdinaryPaletteBirth
open DescentKernelHistory DescentSixParty DescentPrimitivePalette DescentCompiler DescentResetGates
open DescentRawCablePanel DescentSIMDLookup DescentOrdinaryBorn ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
variable (seed Z : ℕ) (op : RotorSpec) (B : Chart)
def word {loc nam width : ℕ} (scale : ℕ) (d : Donor loc nam width) (j : Fin 6) :
    Cell (printedBits G seed Z op) :=
  if d.first then
    if h : scale≤Z then (recover G (fun e=>(d.supplyUnits e).val)).elim 0
      (fun prof=>token G seed Z op (.inr (.inl (⟨scale,Nat.lt_succ_of_le h⟩,prof,j)))) else 0
  else 0

theorem word_genuine {loc nam width : ℕ} (scale : ℕ) (d : Donor loc nam width) (j : Fin 6)
    (p : Profile G.C) (range_ : scale≤Z) (first : d.first=true)
    (supply : ∀e,(d.supplyUnits e).val=(p.1 e).val+G.k) :
    word G seed Z op scale d j=token G seed Z op (.inr (.inl (⟨scale,Nat.lt_succ_of_le range_⟩,p,j))) :=by
  simp [word,first,range_,recover_saved G p _ supply]

theorem malformed {loc nam width : ℕ} (scale : ℕ) (d : Donor loc nam width) (j : Fin 6)
    (missing : ¬ ∃p : Profile G.C,∀e,(d.supplyUnits e).val=(p.1 e).val+G.k) :
    word G seed Z op scale d j=0 :=by
  have noProfile : recover G (fun e=>(d.supplyUnits e).val)=none:=by
    cases tag : recover G (fun e=>(d.supplyUnits e).val) with
    | none => rfl
    | some p => exact (missing ⟨p,(recover_iff G p _).mp tag⟩).elim
  simp [word,noProfile]

def published (i : Fin (fields B)) (chip : Cell B.chipBits) : Cell (printedBits G seed Z op) :=
  let j:=finProdFinEquiv.symm i
  word G seed Z op B.scale (chipDonor B.format chip j.1) j.2

theorem blank (i : Fin (fields B)) : published G seed Z op B i 0=0 :=by
  let j : Fin B.donors×Fin 6:=finProdFinEquiv.symm i
  have empty : (chipDonor B.format (0:Cell B.chipBits) j.1).first=false:=
    DescentOrdinaryBorn.first_zero B.format j.1
  change word G seed Z op B.scale (chipDonor B.format (0:Cell B.chipBits) j.1) j.2=0
  simp only [word,empty,Bool.false_eq_true,ite_false]

theorem absent (x : Fin B.donors) (j : Fin 6) (v : Cell B.chipBits) (dead : (chipDonor B.format v x).first=false) :
    published G seed Z op B (finProdFinEquiv (x,j)) v=0 :=by
  simp only [published,word,Equiv.symm_apply_apply,dead,Bool.false_eq_true,ite_false]

theorem genuine (x : Fin B.donors) (j : Fin 6) (v : Cell B.chipBits) (p : Profile G.C) (scale : B.scale≤Z)
    (born : (chipDonor B.format v x).first=true) (supply : ∀e,((chipDonor B.format v x).supplyUnits e).val=(p.1 e).val+G.k) :
    published G seed Z op B (finProdFinEquiv (x,j)) v=
      token G seed Z op (.inr (.inl (⟨B.scale,Nat.lt_succ_of_le scale⟩,p,j))) :=by
  simp only [published,word,Equiv.symm_apply_apply,born,ite_true,dite_eq_left scale,recover_saved G p _ supply,Option.elim_some]

end
end Hierarchy.DescentOrdinaryPaletteBirth

end OAI
