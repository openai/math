import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMCoreRouteDirectory

namespace OAI
/-! # The three fixed columns for the native route recipes -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
variable {z W k w : ℕ}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "R" => Fintype.card (Slots z D k)

def recipeWord (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ)
    (cj : Columns z D×Fin k→ℕ) (f : Field) (row : ℕ) : ℕ :=
  if bound : row/2<R then
    let v := getSlot o ⟨row/2,bound⟩
    match f with
    | .kind => if row%2=0 then 0 else siteKind v
    | .mode => ((Fintype.equivFin _) (action v).1).val
    | .operand => if row%2=0 then (action v).2 else siteResource ci cj v
  else 0

def recipes (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ)
    (cj : Columns z D×Fin k→ℕ) (raw : Memory w) : Memory w :=
  fun x=>if p.kind.base≤x ∧ x<p.kind.base+2*R then (recipeWord o ci cj .kind (x-p.kind.base):Word w)
    else if p.mode.base≤x ∧ x<p.mode.base+2*R then (recipeWord o ci cj .mode (x-p.mode.base):Word w)
    else if p.operand.base≤x ∧ x<p.operand.base+2*R then (recipeWord o ci cj .operand (x-p.operand.base):Word w)
    else raw x

theorem recipes_frame (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ)
    (cj : Columns z D×Fin k→ℕ) (raw : Memory w) (x : ℕ)
    (free : ∀ f,¬((which p f).base≤x ∧ x<(which p f).base+2*R)) : recipes p o ci cj raw x=raw x := by
  have fk : ¬(p.kind.base ≤ x ∧ x < p.kind.base+2*R) := free .kind
  have fm : ¬(p.mode.base ≤ x ∧ x < p.mode.base+2*R) := free .mode
  have fo : ¬(p.operand.base ≤ x ∧ x < p.operand.base+2*R) := free .operand
  unfold recipes
  rw [ite_eq_right fk, ite_eq_right fm, ite_eq_right fo]

theorem recipes_installed (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ)
    (cj : Columns z D×Fin k→ℕ) (raw : Memory w)
    (fits : ∀f,2*R≤(which p f).size) (wide : 2*R≤2^w)
    (km : p.kind.base+2*R≤p.mode.base) (mo : p.mode.base+2*R≤p.operand.base) :
    Installed p o ci cj (recipes p o ci cj raw) := by
  have read (f : Field) (u : ℕ) (hu : u<2*R) :
      (which p f).read (recipes p o ci cj raw) (u:Word w)=(recipeWord o ci cj f u:Word w) := by
    rw [Bank.read,Fin.val_cast_of_lt (hu.trans_le wide),Nat.mod_eq_of_lt (hu.trans_le (fits f))]
    cases f <;> dsimp only [which, recipes]
    · rw [ite_eq_left (show p.kind.base ≤ p.kind.base+u ∧ p.kind.base+u < p.kind.base+2*R by omega), Nat.add_sub_cancel_left]
    · rw [ite_eq_right (show ¬(p.kind.base ≤ p.mode.base+u ∧ p.mode.base+u < p.kind.base+2*R) by omega),
        ite_eq_left (show p.mode.base ≤ p.mode.base+u ∧ p.mode.base+u < p.mode.base+2*R by omega), Nat.add_sub_cancel_left]
    · rw [ite_eq_right (show ¬(p.kind.base ≤ p.operand.base+u ∧ p.operand.base+u < p.kind.base+2*R) by omega),
        ite_eq_right (show ¬(p.mode.base ≤ p.operand.base+u ∧ p.operand.base+u < p.mode.base+2*R) by omega),
        ite_eq_left (show p.operand.base ≤ p.operand.base+u ∧ p.operand.base+u < p.operand.base+2*R by omega), Nat.add_sub_cancel_left]
  intro i
  have h := i.isLt
  have even : (2*i.val)/2=i.val := by omega
  have odd : (2*i.val+1)/2=i.val := by omega
  have mod0 : 2*i.val%2=0 := by omega
  have mod1 : (2*i.val+1)%2=1 := by omega
  have e := fun f=>read f (2*i.val) (by omega)
  have t := fun f=>read f (2*i.val+1) (by omega)
  have zero : ((0:ℕ) : Word w) = 0 := Fin.ext (by
    change 0 % 2^w = 0
    exact Nat.zero_mod _)
  exact ⟨by simpa only [which, recipeWord, even, dite_eq_left h, mod0, ite_true, Fin.eta, zero] using e .kind,
    by simpa only [which, recipeWord, odd, dite_eq_left h, mod1, ite_eq_right Nat.one_ne_zero, Fin.eta] using t .kind,
    by simpa only [which, recipeWord, even, dite_eq_left h, Fin.eta] using e .mode,
    by simpa only [which, recipeWord, even, dite_eq_left h, mod0, ite_true, Fin.eta] using e .operand,
    by simpa only [which, recipeWord, odd, dite_eq_left h, mod1, ite_eq_right Nat.one_ne_zero, Fin.eta] using t .operand⟩

theorem Installed.transfer {p : Recipes} {o : Orders z D k} {ci : Commodity (Fin (2^z)) N k→ℕ}
    {cj : Columns z D×Fin k→ℕ} {m m' : Memory w} (rom : Installed p o ci cj m)
    (low : ℕ) (keep : ∀x<low,m' x=m x) (upper : ∀f,(which p f).base+(which p f).size≤low) :
    Installed p o ci cj m' := by
  have read (f : Field) (i : Word w) : (which p f).read m' i=(which p f).read m i :=
    keep _ ((Nat.add_lt_add_left (Nat.mod_lt i.val (Nat.two_pow_pos _)) _).trans_le (upper _))
  intro i
  exact ⟨(read .kind _).trans (rom i).1,(read .kind _).trans (rom i).2.1,
    (read .mode _).trans (rom i).2.2.1,(read .operand _).trans (rom i).2.2.2.1,
    (read .operand _).trans (rom i).2.2.2.2⟩

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
