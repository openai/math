import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasTypes
import OAI.Computability.NearSquareRoot.InterchangeCompiledAtlas
import OAI.Computability.NearSquareRoot.InterchangeFlatPackingList

/-!
# Packing the four finite chart families into a flat opcode table

The four intervals have room for every tuple of indices. An endpoint with a
false incidence mask has no typed chart and its slot contains an empty word.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas

open Interchange Interchange.RectangleAtlas Interchange.StageLedger

/-- Empty slots for nonincident rectangle endpoints are included in this capacity. -/
def capacity (m L T : ℕ) := 2*m*L + m*T + 2*L*T + 2*m*L*T

variable {m L T : ℕ} {r : Fin T → Rectangle (Fin L)}

def chartIndex : Chart r m → ℕ
  | .inl (s,j,v) => labelIdx m L s j v
  | .inr (.inl (j,t)) => commonIdx m L T j t
  | .inr (.inr (.inl ⟨s,v,t⟩)) => prepareIdx m L T s v t.val
  | .inr (.inr (.inr (j,⟨s,v,t⟩))) => localIdx m L T s j v t.val

private structure Code (α : Type) where
  size : ℕ
  index : α → ℕ
  bound : ∀ x, index x < size
  inj : Function.Injective index

private def finiteCode (n : ℕ) : Code (Fin n) := ⟨n, Fin.val, Fin.isLt, Fin.val_injective⟩
private def boolCode : Code Bool := ⟨2, Bool.toNat, Bool.toNat_lt, by decide⟩

private def product {α β : Type} (A : Code α) (B : Code β) : Code (α × β) where
  size := A.size * B.size
  index x := A.index x.1 * B.size + B.index x.2
  bound x := calc
    _ < A.index x.1 * B.size + B.size := Nat.add_lt_add_left (B.bound _) _
    _ = (A.index x.1 + 1) * B.size := (Nat.succ_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (A.bound _)
  inj := by
    rintro ⟨x,y⟩ ⟨u,v⟩ h
    change A.index x * B.size + B.index y = A.index u * B.size + B.index v at h
    have hidx : B.index y = B.index v := by
      simpa only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt (B.bound _)]
        using congrArg (· % B.size) h
    have hpos := Nat.zero_lt_of_lt (B.bound y)
    exact Prod.ext (A.inj (Nat.eq_of_mul_eq_mul_right hpos (Nat.add_right_cancel (hidx ▸ h))))
      (B.inj hidx)

private def union {α β : Type} (A : Code α) (B : Code β) : Code (α ⊕ β) where
  size := A.size + B.size
  index := Sum.elim A.index (fun x => A.size + B.index x)
  bound
    | .inl x => (A.bound x).trans_le (Nat.le_add_right ..)
    | .inr x => Nat.add_lt_add_left (B.bound x) _
  inj := by
    rintro (x|x) (y|y) he <;> simp only [Sum.elim_inl, Sum.elim_inr] at he
    · exact congrArg Sum.inl (A.inj he)
    · have := A.bound x
      omega
    · have := A.bound y
      omega
    · exact congrArg Sum.inr (B.inj (Nat.add_left_cancel he))

private def restrict {α β : Type} (A : Code β) (f : α → β) (hf : Function.Injective f) : Code α :=
  ⟨A.size, A.index ∘ f, fun x => A.bound (f x), A.inj.comp hf⟩

private abbrev Endpoints (r : Fin T → Rectangle (Fin L)) := (s : Bool) × Endpoint r s

private def flatten (u : Endpoints r) : (Bool × Fin L) × Fin T := ((u.1,u.2.1),u.2.2.val)

private theorem flatten_injective : Function.Injective (@flatten L T r) := by
  rintro ⟨s,v,t,ht⟩ ⟨s',v',t',ht'⟩ he
  simp only [flatten, Prod.mk.injEq] at he
  rcases he with ⟨⟨rfl,rfl⟩,rfl⟩
  rfl

private def code (r : Fin T → Rectangle (Fin L)) (m : ℕ) : Code (Chart r m) :=
  let M := finiteCode m
  let V := finiteCode L
  let B := finiteCode T
  let label := restrict (product (product boolCode M) V) (fun (x : Bool × Fin m × Fin L) =>
    ((x.1, x.2.1), x.2.2)) (fun ⟨_,_,_⟩ ⟨_,_,_⟩ h => by simpa [and_assoc] using h)
  let prep := restrict (product (product boolCode V) B) flatten flatten_injective
  let loc := restrict (product (product (product boolCode M) V) B)
    (fun (x : Fin m × Endpoints r) => (((x.2.1,x.1),x.2.2.1), x.2.2.2.val)) (by
      rintro ⟨j,s,v,t,ht⟩ ⟨j',s',v',t',ht'⟩ he
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
      rfl)
  union label (union (product M B) (union prep loc))

private theorem chartIndex_eq (c : Chart r m) : chartIndex c = (code r m).index c := by
  rcases c with ⟨s,j,v⟩ | ⟨j,t⟩ | ⟨s,v,t⟩ | ⟨j,s,v,t⟩ <;>
    simp [chartIndex,code,union,restrict,product,flatten,finiteCode,boolCode,labelIdx,commonIdx,
      prepareIdx,localIdx,Nat.add_assoc]

theorem chartIndex_injective : Function.Injective (@chartIndex m L T r) := by
  simpa only [funext chartIndex_eq] using (code r m).inj

theorem chartIndex_lt (c : Chart r m) : chartIndex c < capacity m L T := by
  rw [chartIndex_eq]
  simpa only [capacity,code,union,restrict,product,finiteCode,boolCode,Nat.add_assoc] using
    (code r m).bound c

/-- All chart words in the order expected by the flat verifier. -/
noncomputable def pack (w : Chart r m → Opcode.Word) : List Opcode.Word :=
  PackingList.pack [] chartIndex (capacity m L T) w

@[simp] theorem length_pack (w : Chart r m → Opcode.Word) : (pack w).length = capacity m L T :=
  PackingList.length_pack ..

@[simp] theorem chart_pack (w : Chart r m → Opcode.Word) (c : Chart r m) :
    chart (pack w) (chartIndex c) = w c :=
  PackingList.getD_pack [] chartIndex _ w chartIndex_injective c (chartIndex_lt c)

theorem chart_pack_unused (w : Chart r m → Opcode.Word) (i : ℕ)
    (hi : ∀ c : Chart r m, chartIndex c ≠ i) : chart (pack w) i = [] :=
  PackingList.getD_pack_unused [] chartIndex _ w i hi

end FlatAtlas

end NearSquareRoot
end Computability
end OAI
