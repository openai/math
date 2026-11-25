import OAI.Computability.BorderVNP.CrossingCellProfileRecords

/-!
# Concrete assignment banks for physical profile sites

For the local comparison a bank can be laid out as a finite collection of
fixed-stride rows. Each row stores its blocks consecutively. Padding has the
unique default value false. This realizes the sparse records for every actual
assignment, including zero-width bundles and terms of multiplicity zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Profile.Cell

open CellSparse
open scoped Classical
variable {R : Type*} [Fintype R]

/-- Rectangular slices addressed by sparse ports. -/
structure BankLayout (R : Type*) where
  /-- Number of blocks on each slice. -/
  copies : R → ℕ
  /-- Number of bits in each block. -/
  lanes : R → ℕ

/-- A fixed row stride containing every slice of the bank. -/
def BankLayout.stride (L : BankLayout R) := ∑ r, L.copies r * L.lanes r

/-- Explicit strided port for one slice. -/
noncomputable def BankLayout.port (L : BankLayout R) (r : R) : Port :=
  ⟨(Fintype.equivFin R r).val * L.stride, L.lanes r, 1⟩

/-- The physical block data stored at the addresses in a layout. -/
abbrev BankLayout.Data (L : BankLayout R) := ∀ r, Fin (L.copies r) → Fin (L.lanes r) → Bool

private theorem fits (L : BankLayout R) (r : R) : L.copies r * L.lanes r ≤ L.stride :=
  Finset.single_le_sum (fun i _ => Nat.zero_le (L.copies i * L.lanes i)) (Finset.mem_univ r)

private noncomputable def bitIndex (L : BankLayout R)
    (z : Σ r, Fin (L.copies r) × Fin (L.lanes r)) : Fin (Fintype.card R * L.stride) :=
  finProdFinEquiv (Fintype.equivFin R z.1, (finProdFinEquiv z.2).castLE (fits L z.1))

private theorem bitIndex_injective (L : BankLayout R) : Function.Injective (bitIndex L) := by
  rintro ⟨r, a⟩ ⟨s, b⟩ h
  have he := finProdFinEquiv.injective h
  have hrs : r = s := (Fintype.equivFin R).injective (congrArg Prod.fst he)
  subst s
  have hab : a = b := finProdFinEquiv.injective (Fin.ext (congrArg (fun z => z.2.val) he))
  subst b
  rfl

private theorem bitIndex_val (L : BankLayout R) (r : R) (i : Fin (L.copies r)) (k : Fin (L.lanes r)) :
    (bitIndex L ⟨r, (i, k)⟩).val = (L.port r).atBit i k := by
  change k.val + L.lanes r * i.val + L.stride * (Fintype.equivFin R r).val =
    (Fintype.equivFin R r).val * L.stride + i.val * L.lanes r + k.val * 1
  ring

/-- Every active sparse address is in the allocated finite row bank. -/
theorem BankLayout.atBit_lt (L : BankLayout R) (r : R) (i : Fin (L.copies r))
    (k : Fin (L.lanes r)) : (L.port r).atBit i k < Fintype.card R * L.stride := by
  rw [← bitIndex_val L r i k]
  exact (bitIndex L ⟨r, (i,k)⟩).isLt

/-- Store all the slices and fill every unused bank address with zero. -/
noncomputable def BankLayout.bank (L : BankLayout R) (y : L.Data) : ℕ → Bool :=
  Function.extend (fun z => (bitIndex L z).val) (fun z => y z.1 z.2.1 z.2.2) (fun _ => false)

/-- Reading any lane at its sparse address returns the corresponding physical bit. -/
theorem BankLayout.bank_atBit (L : BankLayout R) (y : L.Data) (r : R)
    (i : Fin (L.copies r)) (k : Fin (L.lanes r)) :
    L.bank y ((L.port r).atBit i k) = y r i k := by
  rw [← bitIndex_val L r i k]
  exact (Fin.val_injective.comp (bitIndex_injective L)).extend_apply _ _ ⟨r, (i,k)⟩

variable {A j b : ℕ}

/-- Terminal rows for the selector, original input, and each compact feeder, respectively. -/
def terminalLayout (j b : ℕ) (p : Fin A → ℕ) : BankLayout (Unit ⊕ Unit ⊕ Fin A) where
  copies := Sum.elim (fun _ => j) (Sum.elim (fun _ => j) p)
  lanes := Sum.elim (fun _ => Nat.clog 2 A) (fun _ => b)

/-- With a genuine histogram the allocated row stride is linear in multiplicity.
It includes the selector, all original slots, and all compact term slots. -/
theorem terminalStride (j b : ℕ) (p : Fin A → ℕ) (hp : ∑ a, p a = j) :
    (terminalLayout j b p).stride = j * (Nat.clog 2 A + 2 * b) := by
  unfold BankLayout.stride
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique]
  change j * Nat.clog 2 A + (j * b + ∑ a, p a * b) = _
  rw [← Finset.sum_mul, hp]
  ring

/-- A terminal's three kinds of physical bit bundles in its sparse layout. -/
def terminalData (p : Fin A → ℕ) (s : Fin j → Fin (Nat.clog 2 A) → Fin 2)
    (f : ∀ a, Fin (p a) → Fin b → Bool) (x : Fin (j*b) → Bool) : (terminalLayout j b p).Data
  | .inl () => fun i k => finTwoEquiv (s i k)
  | .inr (.inl ()) => blocks x
  | .inr (.inr a) => f a

/-- The terminal descriptor expressed entirely in this layout's bit addresses. -/
noncomputable def canonicalTerminalRecord (j b : ℕ) (p : Fin A → ℕ) : Record :=
  let L := terminalLayout j b p
  terminalRecord j b p (L.port (.inl ())) (L.port (.inr (.inl ()))) (fun a => L.port (.inr (.inr a)))

/-- The canonical terminal bank realizes the physical predicate with no address-agreement premise. -/
theorem canonical_terminal_iff (boxes : List (List Factor)) (p : Fin A → ℕ)
    (s : Fin j → Fin (Nat.clog 2 A) → Fin 2) (f : ∀ a, Fin (p a) → Fin b → Bool)
    (x : Fin (j*b) → Bool) :
    (canonicalTerminalRecord j b p).Valid boxes ((terminalLayout j b p).bank (terminalData p s f x)) ↔
      terminalTest p s f x := by
  let L := terminalLayout j b p
  let y := terminalData p s f x
  have hs : selector (A := A) (j := j) (L.bank y) (L.port (.inl ())) = s := by
    funext i k
    exact congrArg finTwoEquiv.symm (L.bank_atBit y (.inl ()) i k) |>.trans (finTwoEquiv.symm_apply_apply _)
  have hf : feeders (b := b) p (L.bank y) (fun a => L.port (.inr (.inr a))) = f := by
    funext a i k
    exact L.bank_atBit y (.inr (.inr a)) i k
  have hx : external (j := j) (b := b) (L.bank y) (L.port (.inr (.inl ()))) = x := by
    apply blocks.injective
    funext i k
    rw [external, Equiv.apply_symm_apply]
    exact L.bank_atBit y (.inr (.inl ())) i k
  change profileValid (L.bank y) j _ _ _ _ ↔ _
  rw [terminal_record_iff, hs, hf, hx]

variable {P : Type} [Fintype P]

/-- The origin has one row of selector blocks per spoke. -/
def originLayout (P : Type) (j A : ℕ) : BankLayout P where
  copies := fun _ => j
  lanes := fun _ => Nat.clog 2 A

/-- Only the fixed number of terminal selector bundles enters the origin stride. -/
theorem originStride (j A : ℕ) : (originLayout P j A).stride =
    Fintype.card P * (j * Nat.clog 2 A) := by
  simp [originLayout, BankLayout.stride]

/-- The canonical origin bank realizes the physical predicate for every spoke assignment. -/
theorem canonical_origin_iff (boxes : List (List Factor)) (p : Fin A → ℕ) (first : P)
    (s : P → Fin j → Fin (Nat.clog 2 A) → Fin 2) :
    (∀ r ∈ originRecords j p first (originLayout P j A).port,
      r.Valid boxes ((originLayout P j A).bank (fun u i k => finTwoEquiv (s u i k)))) ↔
      originTest first p s := by
  rw [origin_records_iff]
  have hs : (fun u => selector (j := j) (A := A)
      ((originLayout P j A).bank (fun u i k => finTwoEquiv (s u i k))) ((originLayout P j A).port u)) = s := by
    funext u i k
    exact congrArg finTwoEquiv.symm ((originLayout P j A).bank_atBit _ u i k) |>.trans
      (finTwoEquiv.symm_apply_apply _)
  rw [hs]

end Crossing.Profile.Cell

end BorderVNP
end Computability
end OAI
