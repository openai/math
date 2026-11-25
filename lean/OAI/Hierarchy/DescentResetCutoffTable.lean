import OAI.Hierarchy.DescentResetThreshold
import OAI.Hierarchy.DescentColonies
import OAI.Hierarchy.DescentPackedPayloadBudget
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # A shared native cutoff lookup from the real traffic sum and the two selected depths -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Cutoff
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w : ℕ}

def levelBank (base levels : ℕ) : Bank := ⟨base,levels⟩
def tableBank (base levels total : ℕ) : Bank := ⟨base+2^levels,levels+total⟩
def finish (base levels total : ℕ) := base+2^levels+2^(levels+total)

/-- Only public scale constants enter this ROM. The two dynamic coordinates come
from the measured prefix depth and the zero-frequency traffic coefficient. -/
def header (base levels total K scale bound : ℕ) (m : Memory w) (z : ℕ) : Word w :=
  if z<base then m z else if z-base<2^levels then (2^total*(z-base):ℕ) else
    if z-(base+2^levels)<2^(levels+total) then
      let idx:=z-(base+2^levels)
      (threshold K scale (idx/2^total) (idx%2^total) bound:ℕ) else m z

def Resident (base levels total K scale bound : ℕ) (m : Memory w) : Prop :=
  (∀j<2^levels,m (base+j)=(2^total*j:ℕ)) ∧
    ∀j<2^levels,∀z<2^total,m (base+2^levels+(2^total*j+z))=(threshold K scale j z bound:ℕ)

theorem index_lt (levels total j z : ℕ) (level : j<2^levels) (data : z<2^total) :
    2^total*j+z<2^(levels+total) := by
  calc
    _<2^total*j+2^total:=Nat.add_lt_add_left data _
    _=2^total*(j+1):=(Nat.mul_succ ..).symm
    _≤2^total*2^levels:=Nat.mul_le_mul_left _ level
    _=_:=by rw [Nat.mul_comm,pow_add]

theorem mounted (base levels total K scale bound : ℕ) (m : Memory w) :
    Resident base levels total K scale bound (header base levels total K scale bound m) := by
  refine ⟨fun j hj=>?_,fun j hj z hz=>?_⟩
  · simp only [header,not_lt.mpr (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left,hj,ite_true]
  · have idx:=index_lt levels total j z hj hz
    have outside : ¬base+2^levels+(2^total*j+z)<base := by omega
    have later : ¬base+2^levels+(2^total*j+z)-base<2^levels := by omega
    simp only [header,outside,ite_false,later,Nat.add_sub_cancel_left,idx,ite_true,
      Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt hz,Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt hz]

theorem frame (base levels total K scale bound : ℕ) (m : Memory w) (z : ℕ) (apart : z<base ∨ finish base levels total≤z) :
    header base levels total K scale bound m z=m z := by
  rcases apart with before|after
  · simp [header,before]
  · unfold finish at after
    have nonnegLevels := Nat.zero_le (2^levels)
    have nonnegTable := Nat.zero_le (2^(levels+total))
    have aboveBase : base ≤ z := by omega
    have aboveLevels : 2^levels ≤ z-base := by omega
    have aboveTable : 2^(levels+total) ≤ z-(base+2^levels) := by omega
    simp only [header,not_lt.mpr aboveBase,not_lt.mpr aboveLevels,not_lt.mpr aboveTable,ite_false]

def level (left right : Expr) : Expr := .branch .lt left right right left
def term (base levels total : ℕ) (left right sum : Expr) : Expr :=
  .lookup (tableBank base levels total) (.op .add (.lookup (levelBank base levels) (level left right)) sum)

theorem read (base levels total K scale bound : ℕ) (left right sum : Expr) (m : Memory w) (p : Word w)
    (j₁ j₂ s : ℕ) (bind : left.eval m p=(j₁:Word w)) (link : right.eval m p=(j₂:Word w))
    (source : sum.eval m p=(s:Word w))
    (levelsFit : max j₁ j₂<2^levels) (sumFit : s<2^total) (width : levels+total≤w)
    (rom : Resident base levels total K scale bound m) :
    (term base levels total left right sum).eval m p=(threshold K scale (max j₁ j₂) s bound:ℕ) := by
  let j:=max j₁ j₂
  have levelWidth : 2^levels≤2^w:=Nat.pow_le_pow_right (by decide) (by omega)
  have jw : j<2^w:=levelsFit.trans_le levelWidth
  have j1 : j₁<2^w:=(le_max_left j₁ j₂).trans_lt jw
  have j2 : j₂<2^w:=(le_max_right j₁ j₂).trans_lt jw
  have tested : DescriptorExpr.Comparison.lt.test (left.eval m p) (right.eval m p)=true ↔ j₁<j₂ := by
    rw [bind,link]
    simp only [DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,
      Fin.val_cast_of_lt j1,Fin.val_cast_of_lt j2]
  have chosen : (level left right).eval m p=(j:Word w) := by
    by_cases less : j₁<j₂
    · calc
        (level left right).eval m p=right.eval m p := ite_eq_left (tested.mpr less)
        _=(j:Word w) := by simpa only [j,max_eq_right less.le] using link
    · calc
        (level left right).eval m p=left.eval m p := ite_eq_right (mt tested.mp less)
        _=(j:Word w) := by simpa only [j,max_eq_left (le_of_not_gt less)] using bind
  have offset : (levelBank base levels).read m (j:Word w)=((2^total*j:ℕ):Word w) := by
    change m (base+(j:Word w).val%2^levels)=_
    rw [Fin.val_cast_of_lt jw,Nat.mod_eq_of_lt (show j<2^levels from levelsFit)]
    exact rom.1 j levelsFit
  have index := index_lt levels total j s levelsFit sumFit
  have fits := index.trans_le (Nat.pow_le_pow_right (by decide) width)
  change (tableBank base levels total).read m (BinaryOp.add.eval
    ((levelBank base levels).read m ((level left right).eval m p)) (sum.eval m p))=_
  rw [chosen,offset,source]
  change (tableBank base levels total).read m (((2^total*j:ℕ):Word w)+(s:Word w))=_
  rw [←Nat.cast_add]
  change m (base+2^levels+((2^total*j+s:ℕ):Word w).val%2^(levels+total))=_
  rw [Fin.val_cast_of_lt fits,Nat.mod_eq_of_lt index]
  exact rom.2 j levelsFit s sumFit

theorem bound_words (base levels total h : ℕ) (space : levels+total≤h/2) :
    finish base levels total-base≤2*2^(h/2) := by
  have one : 2^(levels+total) ≤ 2^(h/2) := Nat.pow_le_pow_right (by decide) space
  have a : 2^levels ≤ 2^(h/2) := Nat.pow_le_pow_right (by decide) (by omega : levels≤h/2)
  unfold finish
  have nonnegLevels := Nat.zero_le (2^levels)
  have nonnegTable := Nat.zero_le (2^(levels+total))
  omega

theorem total_fits {m bits : ℕ} (traffic : DescentColonies.Block m→ℕ) (bound : ∀x,traffic x<2^bits) :
    (∑x,traffic x)<2^(m+bits) := by
  calc
    _ < ∑_x : DescentColonies.Block m,2^bits := Finset.sum_lt_sum (fun i _=>(bound i).le) ⟨0,Finset.mem_univ _,bound 0⟩
    _=_ := by simp [pow_add]

end
end Hierarchy.DescentPlainTerminal.Suffix.Cutoff

end OAI
