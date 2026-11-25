import OAI.ThreeFlat.Diagonal.TraceMaskDictionary
import OAI.ThreeFlat.RAM.EffectSeedProcedure

namespace OAI
/-! # One sparse startup for the local LUT IDs, XOR offsets and inverse offset dictionary -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout
open Computability.VPVNP.BurstRAM RAM RAM.EffectStream
open scoped Fin.CommRing
variable {F : Type*} {p k low o c n W : ℕ} {N : BitNetwork F p} (P : RowLayout N k low o c)

abbrev SeedKey (n o : ℕ) := Fin n ⊕ (Fin o ⊕ Fin o)

def seedAddress (ids masks dict : ℕ) : SeedKey n o → ℕ
  | .inl i => ids+i.val
  | .inr (.inl i) => masks+i.val
  | .inr (.inr i) => dict+(P.offset i).val

def seedValue (lookup : Fin n→ℕ) : SeedKey n o → ℕ
  | .inl i => lookup i
  | .inr (.inl i) => (P.offset i).val
  | .inr (.inr i) => (firstIndex P.offset i).val

noncomputable def seedRecords (ids masks dict : ℕ) (lookup : Fin n→ℕ) : List (Record W) :=
  List.ofFn fun i : Fin (Fintype.card (SeedKey n o)) =>
    let j := (Fintype.equivFin (SeedKey n o)).symm i
    ((P.seedAddress ids masks dict j : Word W),(P.seedValue lookup j : Word W))

@[simp] theorem seedRecords_length (ids masks dict : ℕ) (lookup : Fin n→ℕ) :
    (P.seedRecords (W:=W) ids masks dict lookup).length=n+(o+o) := by
  simp [seedRecords,SeedKey]

theorem seedRecords_mem (ids masks dict : ℕ) (lookup : Fin n→ℕ) (x : Record W) :
    x ∈ P.seedRecords ids masks dict lookup ↔
      ∃ j, ((P.seedAddress ids masks dict j : Word W),(P.seedValue lookup j : Word W))=x := by
  constructor
  · intro hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact ⟨_,rfl⟩
  · rintro ⟨j,rfl⟩
    apply List.mem_ofFn.mpr
    exact ⟨(Fintype.equivFin (SeedKey n o)) j,by simp⟩

structure SeedRoom (n o rows ids masks dict : ℕ) (W : ℕ) : Prop where
  labelEnd : ids+n≤ masks
  maskEnd : masks+o≤dict
  wordEnd : dict+rows≤2^W

theorem seedAddress_range (ids masks dict : ℕ) (room : SeedRoom n o (2^k*2^low) ids masks dict W)
    (j : SeedKey n o) : ids≤P.seedAddress ids masks dict j ∧ P.seedAddress ids masks dict j<dict+2^k*2^low := by
  have l := room.labelEnd
  have m := room.maskEnd
  rcases j with a|a|a <;> simp only [seedAddress]
  · have := a.isLt; omega
  · have := a.isLt; omega
  · have := (P.offset a).isLt; omega

private theorem seedValue_congr (ids masks dict : ℕ) (lookup : Fin n→ℕ)
    (room : SeedRoom n o (2^k*2^low) ids masks dict W) {i j : SeedKey n o}
    (hit : P.seedAddress ids masks dict i=P.seedAddress ids masks dict j) :
    P.seedValue lookup i=P.seedValue lookup j := by
  have hl := room.labelEnd
  have hm := room.maskEnd
  rcases i with i|i|i <;> rcases j with j|j|j <;> simp only [seedAddress] at hit <;>
    first
    | exact congrArg lookup (Fin.ext (by omega))
    | exact congrArg (fun x : Fin o => (P.offset x).val) (Fin.ext (by omega))
    | exact congrArg Fin.val (firstIndex_congr P.offset (Fin.ext (by omega)))
    | (have hi := i.isLt; have hj := j.isLt; omega)

theorem seed_read (ids masks dict : ℕ) (lookup : Fin n→ℕ) (m : Memory W)
    (room : SeedRoom n o (2^k*2^low) ids masks dict W) (j : SeedKey n o) :
    after m (events (P.seedRecords ids masks dict lookup)) (P.seedAddress ids masks dict j) =
      (P.seedValue lookup j : Word W) := by
  apply after_at
  · intro x hx hit
    obtain ⟨i,rfl⟩ := (P.seedRecords_mem ids masks dict lookup x).mp hx
    have small := (P.seedAddress_range ids masks dict room i).2.trans_le room.wordEnd
    change ((P.seedAddress ids masks dict i : Word W)).val=P.seedAddress ids masks dict j at hit
    rw [Fin.val_cast_of_lt small] at hit
    exact congrArg (fun a : ℕ => (a : Word W)) (P.seedValue_congr ids masks dict lookup room hit)
  · right
    refine ⟨_,(P.seedRecords_mem ids masks dict lookup _).mpr ⟨j,rfl⟩,?_⟩
    exact Fin.val_cast_of_lt ((P.seedAddress_range ids masks dict room j).2.trans_le room.wordEnd)

theorem seed_safe (ids masks dict tmp : ℕ) (lookup : Fin n→ℕ)
    (room : SeedRoom n o (2^k*2^low) ids masks dict W)
    (apart : tmp+2*(n+(o+o))≤ ids ∨ dict+2^k*2^low≤tmp) :
    Safe tmp (P.seedRecords (W:=W) ids masks dict lookup) := by
  intro x hx
  obtain ⟨j,rfl⟩ := (P.seedRecords_mem ids masks dict lookup x).mp hx
  have a := P.seedAddress_range ids masks dict room j
  rw [P.seedRecords_length]
  change ((P.seedAddress ids masks dict j : Word W)).val<tmp ∨ tmp+2*(n+(o+o))≤((P.seedAddress ids masks dict j : Word W)).val
  rw [Fin.val_cast_of_lt (a.2.trans_le room.wordEnd)]
  omega

theorem seed_outside (ids masks dict : ℕ) (lookup : Fin n→ℕ) (m : Memory W)
    (room : SeedRoom n o (2^k*2^low) ids masks dict W) (a : ℕ)
    (away : a< ids ∨ dict+2^k*2^low≤a) :
    after m (events (P.seedRecords ids masks dict lookup)) a=m a := by
  apply after_at _ _ _ _ _ (Or.inl rfl)
  intro x hx hit
  obtain ⟨j,rfl⟩ := (P.seedRecords_mem ids masks dict lookup x).mp hx
  have aj := P.seedAddress_range ids masks dict room j
  change ((P.seedAddress ids masks dict j : Word W)).val=a at hit
  rw [Fin.val_cast_of_lt (aj.2.trans_le room.wordEnd)] at hit
  omega


end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
