import OAI.LinearAlgebra.SpectralBooks.RawTiledTables
import OAI.Hierarchy.CorrectionProducts

namespace OAI
/-! # Ordinary sums through successive physical wire replacements

A replacement uses one coefficient table on the original site legs for each
choice. The table is a signed local image of the actual installed chord
widths. Binding replacements keeps all previous matrices, and expands the
wire that those matrices previously used into its own ordinary sum.
-/

noncomputable section
set_option maxHeartbeats 1200000
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical BigOperators
variable {F : Type*} [Field F] {S : ℕ}

structure Expansion (T : Raw.{0} (Fin S) F) (C : Type) [Fintype C] (ends : C → Widths S) where
  part : C → (∀ i,T.Leg i) → F
  sum : T.coeff = ∑ c, part c
  image : ∀ c, ({T with coeff := part c} : Raw (Fin S) F).Restricts (raw F (ends c))

namespace Expansion
variable {T : Raw.{0} (Fin S) F} {C : Type} [Fintype C] {ends : C → Widths S}

/-- A deterministic transport has one summand. This includes identity steps,
residual routing, and local changes of the incident wire order. -/
def transport (U : Widths S) (route : T.Restricts (raw F U)) : Expansion T Unit (fun _=>U) where
  part _ := T.coeff
  sum := by simp
  image _ := route

def matrices (E : Expansion T C ends) (c : C) :
    ∀ i,T.Leg i → State (ends c) i → F := (E.image c).choose

/-- Changing the finite enumeration of a complete state leaves its sum unchanged. -/
private theorem full_sum {A : Type*} (l r : Fintype A) (f : A→F) :
    (@Finset.univ A l).sum f=(@Finset.univ A r).sum f := by
  have eq : l=r := Subsingleton.elim _ _
  cases eq
  rfl

theorem action (E : Expansion T C ends) (c : C) (x : ∀ i,T.Leg i) :
    E.part c x = ∑ y : ∀ i, State (ends c) i, (raw F (ends c)).coeff y *
      ∏ i, E.matrices c i (x i) (y i) := by
  refine ((E.image c).choose_spec x).trans ?_
  exact full_sum _ _ _

theorem atPoint (E : Expansion T C ends) (x : ∀i,T.Leg i) : T.coeff x=∑ c,E.part c x := by
  simpa only [Finset.sum_apply] using congrFun E.sum x

/-- Expand the central installed wires while preserving every outer matrix. -/
def bind {D : C → Type} [∀ c,Fintype (D c)] {dest : (c : C) → D c → Widths S}
    (E : Expansion T C ends) (N : ∀ c, Expansion (raw F (ends c)) (D c) (dest c)) :
    Expansion T (Σ c,D c) (fun a => dest a.1 a.2) where
  part a x := ∑ y : ∀ i,State (ends a.1) i, (N a.1).part a.2 y *
    ∏ i, E.matrices a.1 i (x i) (y i)
  sum := by
    funext x
    rw [E.sum,Finset.sum_apply,Finset.sum_apply,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    rw [E.action c x]
    have pt (y : ∀i,State (ends c) i) : (raw F (ends c)).coeff y=∑ b,(N c).part b y :=
      (N c).atPoint y
    simp_rw [pt,Finset.sum_mul]
    exact Finset.sum_comm
  image := by
    rintro ⟨c,b⟩
    refine restrict_trans (B:=State (ends c)) (Y:=(N c).part b) ?_ ((N c).image b)
    refine ⟨E.matrices c,fun x => ?_⟩
    exact full_sum _ _ _

/-- Route the leftover commodities after the last signed choice. This uses
one physical routing restriction per leaf and adds no selector. -/
def finish (E : Expansion T C ends) {lastWire : C → Widths S}
    (route : ∀ c,(raw F (ends c)).Restricts (raw F (lastWire c))) : Expansion T C lastWire where
  part := E.part
  sum := E.sum
  image c := restrict_trans (E.image c) (route c)

/-- Independent balls, retained geometry and any residual wires share a
single physical site set. Each selector chooses exactly one option per
tile, and the installed bit masks are the literal sums of that tile's widths. -/
def simultaneous {t : ℕ} {J : Fin t → Type} [∀ j,Fintype (J j)]
    {input : Fin t → Widths S} {output : ∀ j,J j → Widths S}
    (E : ∀ j, Expansion (raw F (input j)) (J j) (output j)) :
    Expansion (raw F (∑ j,input j)) (∀ j,J j) (fun w => ∑ j,output j (w j)) where
  part w x := ∏ j, (E j).part (w j) (fun i=>blockPortState input i (x i) j)
  sum := by
    funext x
    rw [Finset.sum_apply]
    refine (raw_sum_coeff F input x).trans ?_
    let val (j : Fin t) (b : J j) := (E j).part b (fun i=>blockPortState input i (x i) j)
    refine Eq.trans (b:=∏ j,∑ b,val j b) (Finset.prod_congr rfl (fun j _=>(E j).atPoint _)) ?_
    exact Fintype.prod_sum val
  image := by
    intro w
    refine ⟨tiledTable (fun j => (E j).matrices (w j)),fun x => ?_⟩
    have action := tiledTable_action (fun j => (E j).matrices (w j))
      (fun j=> (E j).part (w j)) (fun j=> (E j).action (w j)) x
    refine action.trans ?_
    exact full_sum _ _ _

end Expansion

/-- The ownership partition of a scheduled round. One tile can be the
untouched remainder with a single deterministically transported option.
The branch equivalence links the controller's native branch to its exact
tuple of local replacement choices. -/
structure Round (F : Type*) [Field F] (source : Widths S) (C : Type) [Fintype C]
    (target : C → Widths S) where
  blocks : ℕ
  demand : Fin blocks → Widths S
  options : Fin blocks → Type
  [finiteOptions : ∀j,Fintype (options j)]
  installed : ∀j,options j → Widths S
  tile : ∀j,Expansion (raw F (demand j)) (options j) (installed j)
  selected : C ≃ (∀j,options j)
  owns_source : source=∑ j,demand j
  owns_target : ∀c,target c=∑ j,installed j (selected c j)
attribute [instance] Round.finiteOptions

def Round.assemble {source : Widths S} {C : Type} [Fintype C] {target : C → Widths S}
    (R : Round F source C target) : Expansion (raw F source) C target := by
  let e := Expansion.simultaneous R.tile
  have hh : Expansion (raw F (∑ j,R.demand j)) C target := by
    refine ⟨fun c=>e.part (R.selected c),e.sum.trans (R.selected.sum_comp e.part).symm,?_⟩
    intro c
    rw [R.owns_target]
    exact e.image (R.selected c)
  exact R.owns_source.symm ▸ hh

private def optionsWithRest {t : ℕ} (J : Fin t → Type) : Fin (t+1) → Type :=
  Fin.cases Unit J

@[instance_reducible]
private def optionsWithRestFinite {t : ℕ} (J : Fin t → Type) [finite : ∀j,Fintype (J j)] :
    ∀j,Fintype (optionsWithRest J j) :=
  Fin.cases (motive := fun j=>Fintype (optionsWithRest J j)) (inferInstanceAs (Fintype Unit)) finite

/-- Select all the physical ball replacements in parallel and transport the
remaining wires once. The single empty selector on the remainder introduces
no multiplicity into the public path. -/
def withRemainder {t : ℕ} {J : Fin t → Type} [∀j,Fintype (J j)]
    (demand : Fin t → Widths S) (installed : ∀j,J j → Widths S)
    (tiles : ∀j,Expansion (raw F (demand j)) (J j) (installed j))
    (restBefore restAfter : Widths S) (rest : (raw F restBefore).Restricts (raw F restAfter)) :
    Round F (restBefore+∑ j,demand j) (∀j,J j) (fun c=>restAfter+∑ j,installed j (c j)) := by
  let opt := optionsWithRest J
  letI : ∀ j,Fintype (opt j) := optionsWithRestFinite J
  let inp : Fin (t+1) → Widths S := Fin.cases restBefore demand
  let out : ∀j,opt j → Widths S := Fin.cases (fun _ : Unit=>restAfter) installed
  let choice : (∀j,J j) ≃ (∀j,opt j) :=
    { toFun := fun c=>Fin.cases () c
      invFun := fun c j=>c j.succ
      left_inv := fun _=>rfl
      right_inv := fun c=>by
        funext j
        induction j using Fin.cases with
        | zero => exact @Subsingleton.elim Unit inferInstance _ _
        | succ j => rfl }
  exact {
    blocks := t+1
    demand := inp
    options := opt
    installed := out
    tile := Fin.cases (Expansion.transport restAfter rest) tiles
    selected := choice
    owns_source := by rw [Fin.sum_univ_succ]; rfl
    owns_target := fun c=>by rw [Fin.sum_univ_succ]; rfl }

/-- Directly debit the simultaneously selected balls' owned physical slots
and retain the balance of each chord unchanged. -/
def repair {t : ℕ} {J : Fin t → Type} [∀j,Fintype (J j)]
    (stock : Widths S) (demand : Fin t → Widths S) (installed : ∀j,J j → Widths S)
    (allocated : ∑ j,demand j ≤ stock)
    (tiles : ∀j,Expansion (raw F (demand j)) (J j) (installed j)) :
    Round F stock (∀j,J j) (fun c=>(stock-∑ j,demand j)+∑ j,installed j (c j)) := by
  let tail := stock-∑ j,demand j
  have balance : tail+∑ j,demand j = stock := tsub_add_cancel_of_le allocated
  exact cast (congrArg (fun source=>Round F source (∀ j,J j) (fun c=>tail+∑ j,installed j (c j))) balance)
    (withRemainder demand installed tiles tail tail (restrict_refl _))

end Hierarchy.WireTelescope

end
end OAI
