import OAI.Computability.NearSquareRoot.InterchangeMinorVerifier
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPRMatrix

/-! # Primitive-recursive minor verification on numerical row-major tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.NumericMinor

open NearSquareRoot.InterchangeROMRepair.Raw

abbrev Picks := List ℕ
def index (s : Picks) (i : ℕ) := s.getD i 0
def entries (A : Mat) (u v : ℕ → ℕ) : Mat := fun i j => A (u i) (v j)
def picks (l h : ℕ) (s : Picks) : Prop :=
  (∀ i < h, index s i < l) ∧ ∀ i < h, ∀ j < h, index s i = index s j → i=j
instance (l h : ℕ) (s : Picks) : Decidable (picks l h s) :=
  inferInstanceAs (Decidable ((_ ∧ _) : Prop))

def laws (p l h : ℕ) (A M : Mat) (s t : Picks) : Prop :=
  picks l h s ∧ picks l h t ∧
  equalMod p h h (mult h (entries A (index s) (index t)) M) ident ∧
  equalMod p l l (mult h (mult h (entries A id (index t)) M) (entries A (index s) id)) A

instance (p l h : ℕ) (A M : Mat) (s t : Picks) : Decidable (laws p l h A M s t) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _ ∧ _) : Prop))

variable {X : Type*} [Primcodable X]

theorem primrec_index {s : X → Picks} {i : X → ℕ} (hs : Primrec s) (hi : Primrec i) :
    Primrec fun x => index (s x) (i x) :=
  (Primrec.list_getD 0).comp hs hi

private theorem primrec_picks {l h : X → ℕ} {s : X → Picks} (hl : Primrec l) (hh : Primrec h)
    (hs : Primrec s) : PrimrecPred fun x => picks (l x) (h x) (s x) := by
  apply PrimrecPred.and
  · exact bounded hh (Primrec.nat_lt.comp (primrec_index (hs.comp .fst) .snd) (hl.comp .fst))
  · apply bounded hh
    apply bounded (hh.comp .fst)
    let P := Primrec.snd.comp (Primrec.fst (α:=X×ℕ) (β:=ℕ))
    let L := (hs.comp (Primrec.fst.comp (Primrec.fst (α:=X×ℕ) (β:=ℕ))))
    exact ((Primrec.eq.comp (primrec_index L P) (primrec_index L .snd)).not.or
      (Primrec.eq.comp P .snd)).of_eq fun _ => by tauto


theorem primrec_entries {A : X → Mat} {u v : X → ℕ → ℕ} (ha : EntryPR A)
    (hu : Primrec₂ u) (hv : Primrec₂ v) : EntryPR fun x => entries (A x) (u x) (v x) :=
  ha.eval .fst (hu.comp .fst (Primrec.fst.comp .snd)) (hv.comp .fst (Primrec.snd.comp .snd))

theorem primrec_laws {p l h : X → ℕ} {A M : X → Mat} {s t : X → Picks}
    (hp : Primrec p) (hl : Primrec l) (hh : Primrec h) (hA : EntryPR A) (hM : EntryPR M)
    (hs : Primrec s) (ht : Primrec t) : PrimrecPred fun x => laws (p x) (l x) (h x) (A x) (M x) (s x) (t x) := by
  have u := (primrec_index (hs.comp .fst) .snd).to₂
  have v := (primrec_index (ht.comp .fst) .snd).to₂
  exact (primrec_picks hl hh hs).and ((primrec_picks hl hh ht).and
    ((primrec_matches hp hh hh ((primrec_entries hA u v).mult hh hM) primrec_ident).and
      (primrec_matches hp hl hl (((primrec_entries hA .right v).mult hh hM).mult hh
        (primrec_entries hA u .right)) hA)))

def encode {l h : ℕ} (s : Fin h → Fin l) : Picks := List.ofFn fun i => (s i).val

@[simp] theorem index_encode {l h : ℕ} (s : Fin h → Fin l) (i : Fin h) : index (encode s) i = s i := by
  unfold index encode
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

theorem picks_encode {l h : ℕ} (s : Fin h → Fin l) : picks l h (encode s) ↔ Function.Injective s := by
  constructor
  · intro h x y e
    exact Fin.ext (h.2 x x.isLt y y.isLt (by simpa using congrArg Fin.val e))
  · intro inj
    constructor
    · intro i hi; exact (index_encode s ⟨i,hi⟩).trans_lt (s ⟨i,hi⟩).isLt
    · intro i hi j hj e
      exact congrArg Fin.val (inj (a₁:=⟨i,hi⟩) (a₂:=⟨j,hj⟩) (Fin.ext <| (index_encode s ⟨i,hi⟩).symm.trans
        (e.trans (index_encode s ⟨j,hj⟩))))

def selected {l h : ℕ} (s : Picks) (hs : picks l h s) (i : Fin h) : Fin l :=
  ⟨index s i,hs.1 i i.isLt⟩

theorem laws_iff {p l h : ℕ} [Fact (p+1).Prime] (A M : Mat) (s t : Picks)
    (hs : picks l h s) (ht : picks l h t) :
    laws p l h A M s t ↔ MinorROM.valid (interpret p l l A)
      ⟨selected s hs,selected t ht,interpret p h h M⟩ = true := by
  have hinj {u : Picks} (hu : picks l h u) : Function.Injective (selected u hu) := fun i j eq =>
    Fin.ext (hu.2 i i.isLt j j.isLt (congrArg Fin.val eq))
  rw [MinorROM.valid_iff]
  simp only [laws,hs,ht,true_and,hinj,matches_iff,interpret_mult,interpret_ident]
  rfl

end Interchange.NumericMinor

end NearSquareRoot
end Computability
end OAI
