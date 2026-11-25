import OAI.Hierarchy.DescentPrimitivePaletteLabels
import OAI.Hierarchy.DescentSeedHistory
import OAI.Hierarchy.DescentSeedHubTrivalence
import OAI.Hierarchy.DescentSeedInternal

namespace OAI
/-! # The one shared structural equality at each genuine exterior stack -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentInitialHost DescentPhysicalSplit DescentSixParty
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P : Type} [Fintype P]
variable (N : Network d P (fun _=>1)) (T : N.Tables F)


def seedRead {s : ℕ} : SeedTag s→List (List Bool)→F
  | .inl h,v=>censusScalar h v
  | .inr _,v=>if v.getD 0 []=v.getD 1 [] then 1 else 0

theorem stack_equal {s w : ℕ} (x y : Word (s*w)) :
    (∏i : Fin s,(if rowAt x i=rowAt y i then (1:F) else 0))=if x=y then 1 else 0 := by
  by_cases agree : x=y
  · simp [agree]
  · have failed : ∃i : Fin s,rowAt x i≠rowAt y i := by
      by_contra! all
      apply agree
      funext j
      obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective j
      exact congrFun (all i) t
    obtain ⟨i,hi⟩ := failed
    rw [ite_eq_right agree]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

def equalityRecipe (s : ℕ) (p : P) : Recipe (SeedTag s) (Boundary (stacked (hubbed N) s) (.inr p)) :=
  atom (.inr ()) 2 (Fin.cons (.inl ⟨.inr p,Or.inr rfl⟩) (fun _=>.inr ⟨p,rfl⟩))

theorem equalityRecipe_read (s : ℕ) (p : P) (z x) :
    (equalityRecipe N s p).value (seedRead (F:=F)) (input (stacked (hubbed N) s) z x)=
      stackTable (hubbed N) (hubTables N T) (.inr p) z x := by
  rw [equalityRecipe,atom_value]
  let a := z ⟨.inr p,Or.inr rfl⟩
  let b := x ⟨p,rfl⟩
  change (if wordList a=wordList b then (1:F) else 0)=∏i : Fin s,if rowAt a i=rowAt b i then 1 else 0
  refine Eq.trans ?_ ((stack_equal (F:=F) (s:=s) (w:=1) a b).symm.trans ?_)
  · have indicator {p q : Prop} (dp : Decidable p) (dq : Decidable q) (equiv : p ↔ q) :
        @ite F p dp 1 0 = @ite F q dq 1 0 := by
      cases dp with
      | isTrue hp =>
        cases dq with
        | isTrue _ => rfl
        | isFalse hq => exact (hq (equiv.mp hp)).elim
      | isFalse hp =>
        cases dq with
        | isTrue hq => exact (hp (equiv.mpr hq)).elim
        | isFalse _ => rfl
    exact indicator _ _ (show wordList a=wordList b ↔ a=b from List.ofFn_inj)
  · apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun d : Decidable (rowAt a i = rowAt b i) =>
      @ite F _ d 1 0) (Subsingleton.elim _ _)

private abbrev seedBase (core : Finset (hubbed N).Edge) : MarkedWorld F d P (fun _=>1) :=
  ⟨⟨hubbed N,hubTables N T⟩,core⟩

private abbrev retainInside : (hubbed N).Site → Bool :=
  Sum.elim (fun _ : N.Site => true) (fun _ : P => false)

def seedHistory (core : Finset (hubbed N).Edge) (s : ℕ) (tri : N.Trivalent)
    (h : (Histories.seedInternal (seedBase N T core) s (retainInside N)).Choice) (v : (hubbed N).Site) :
    Recipe (SeedTag s) (Boundary (stacked (hubbed N) s) v) :=
  match v with
  | .inl u =>
    let r := censusRecipe (hubbed N) (DescentSeedRoot.hubbed_trivalent N tri) (.inl u) (h (.inl u))
    {r with tag:=Sum.inl ∘ r.tag}
  | .inr p => equalityRecipe N s p

theorem hub_seed_represents (core : Finset (hubbed N).Edge) (s : ℕ) (tri : N.Trivalent)
    (h : (Histories.seedInternal (seedBase N T core) s (retainInside N)).Choice) :
    Represents (stacked (hubbed N) s) seedRead
      ((Histories.seedInternal (seedBase N T core) s (retainInside N)).state h).tables
      (seedHistory N T core s tri h) := by
  let counts : ∀v,Count (hubbed N) s v
    | .inl u => h (.inl u)
    | .inr _ => fun _ => 0
  intro v z x
  cases v with
  | inl u =>
    exact census_represents (hubbed N) s (DescentSeedRoot.hubbed_trivalent N tri) counts (.inl u) z x
  | inr p => exact equalityRecipe_read N T s p z x

end
end Hierarchy.DescentKernelHistory

end OAI
