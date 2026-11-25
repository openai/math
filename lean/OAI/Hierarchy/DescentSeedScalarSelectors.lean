import OAI.Hierarchy.DescentSeedMarkedGraph
import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentSeedTrivalentMenu
import OAI.Hierarchy.DescentSeedTokenNumbers
import OAI.Hierarchy.DescentInitialPackage

namespace OAI
/-! # Original seed coefficient and the authentic finite census-bit inputs -/
namespace Hierarchy.DescentSeedRoot
open DescentInitialHost DescentSixParty Computability.BorderVNP.Crossing
open ThreeFlat Routing Catalyst CorrectionBatch
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
/-- Absorbing the pin into a tether at an ordinary site preserves each bit in its old
pattern; there are no remaining attached external pins at the ordinary site. -/
def hubPattern {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1)) (v : N.Site) :
    Pattern (hubbed N) (.inl v) ↪ Pattern N v where
  toFun x := (fun e=>x.1 ⟨.inl e.1,e.2.imp (congrArg Sum.inl) (congrArg Sum.inl)⟩,
    fun p=>x.1 ⟨.inr p.1,Or.inl (congrArg Sum.inl p.2)⟩)
  inj' a b eq := by
    apply Prod.ext
    · funext e t
      rcases e with ⟨e|p,belongs⟩
      · have h : N.src e=v ∨ N.dst e=v := belongs.imp Sum.inl.inj Sum.inl.inj
        exact congrFun (congrFun (congrArg Prod.fst eq) ⟨e,h⟩) t
      · have h : N.attach p=v := belongs.elim Sum.inl.inj (fun no=>(Sum.inr_ne_inl no).elim)
        exact congrFun (congrFun (congrArg Prod.snd eq) ⟨p,h⟩) t
    · funext e
      exact (Sum.inr_ne_inl e.2).elim

theorem hub_patterns {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1))
    (tri : N.Trivalent) (v : N.Site) : Fintype.card (Pattern (hubbed N) (.inl v))≤8 :=
  (Fintype.card_le_of_embedding (hubPattern N v)).trans (patterns_le_eight N tri v)

theorem hub_patterns_card {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1))
    (tri : N.Trivalent) (v : N.Site) (sites : Fintype (Pattern (hubbed N) (.inl v))) :
    @Fintype.card _ sites ≤ 8 := by
  have transfer {original : Fintype (Pattern (hubbed N) (.inl v))}
      (bound : @Fintype.card _ original ≤ 8) : @Fintype.card _ sites ≤ 8 :=
    (@Fintype.card_congr _ _ sites original (Equiv.refl _)).le.trans bound
  exact transfer (hub_patterns N tri v)

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "N" => X.network.copyGraph
local notation "A" => markedInput X
abbrev LocalPattern (v : Old X) := Pattern (A).graph (.inl v)

theorem patterns (v : Old X) : Fintype.card (LocalPattern X v) ≤ 8 := by
  exact @hub_patterns_card 0 (Fin (Fintype.card (Port p X.width))) _ N
    (physical_output X).1 v (inferInstance : Fintype (LocalPattern X v))

def code {v : Old X} (q : LocalPattern X v) : Fin 8 :=
  ((Fintype.equivFin _ q).castLE (patterns X v))

def lookup (v : Old X) (i : Fin 8) : Option (LocalPattern X v) :=
  if h : i.val<Fintype.card (LocalPattern X v) then some ((Fintype.equivFin _).symm ⟨i.val,h⟩) else none

@[simp] theorem lookup_code {v : Old X} (q : LocalPattern X v) :
    lookup X v (code X q)=some q := by
  let e := Fintype.equivFin (LocalPattern X v)
  have inside : (code X q).val < Fintype.card (LocalPattern X v) := (e q).isLt
  unfold lookup
  split
  · apply congrArg some
    apply e.injective
    change e (e.symm _) = e q
    exact (e.apply_symm_apply _).trans (Fin.ext rfl)
  · rename_i missing
    exact (missing inside).elim

/-- One free-field literal per true original local truth-table row. The scalar is a
fixed coefficient of X; only the exponent read from the selected census varies. -/
def coefficient (v : Old X) (i : Fin 8) : F :=
  ((lookup X v i).map (fun q=>coeff (A).graph (A).tables (.inl v) q)).getD 1

abbrev CountKey (R : ℕ) := Fin R × (Σ v : Old X,LocalPattern X v)

/-- Only the low count digits are selected. All unused count rows and the high
guard bits of a word are fixed by the input-independent map. -/
abbrev Select (R s : ℕ) := (Fin R × (Σ v : Old X,LocalPattern X v)) × Fin (digitsNeeded s)

variable {R : ℕ}
def originalScalar (q : CountKey X R) : F := coefficient X q.2.1 (code X q.2.2)

theorem select_card (R s : ℕ) :
    Fintype.card (Select X R s) ≤ R*(Fintype.card (Old X)*8)*digitsNeeded s := by
  classical
  have card : Fintype.card (Σ v : Old X,LocalPattern X v) ≤ Fintype.card (Old X)*8 := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : Old X, (8:ℕ) := Finset.sum_le_sum fun v _=>patterns X v
      _ = _ := by simp
  simpa only [Select,Fintype.card_prod,Fintype.card_fin] using
    Nat.mul_le_mul_right (digitsNeeded s) (Nat.mul_le_mul_left R card)

theorem select_bound (R s : ℕ) :
    Fintype.card (Select X R s) ≤ 80*R*(X.size+1)*(s.log2+1) := by
  have paid := («initialize» X).2.1
  change Fintype.card (Vertex X)+Fintype.card (Cable X)+Fintype.card (Port p X.width) ≤ 10*(X.size+1) at paid
  have part : Fintype.card (Old X) ≤ Fintype.card (Vertex X) :=
    Fintype.card_le_of_embedding ⟨Sum.inl,Sum.inl_injective⟩
  have fixed : Fintype.card (Old X)≤10*(X.size+1) := by omega
  apply (select_card X R s).trans
  apply Nat.mul_le_mul_right
  calc
    _ ≤ R*((10*(X.size+1))*8) := Nat.mul_le_mul_left R (Nat.mul_le_mul_right 8 fixed)
    _ = _ := by ring

end
end Hierarchy.DescentSeedRoot

end OAI
