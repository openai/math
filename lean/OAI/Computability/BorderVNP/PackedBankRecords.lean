import OAI.Computability.BorderVNP.PackedBankRecordWords

/-! # Origin and terminal descriptors assembled from the public words

The generated ports use the computed row addresses. Each row has one suffix
zero check. On the unique padded bank the whole generated list checks exactly
the local predicate of the physical network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCircuit

open Crossing.Profile Crossing.Profile.Cell CellSparse
open scoped Classical

variable {D A : ℕ} (b : ℕ)

/-- Reconstruct the strided port from its publicly computed base and fixed lane count. -/
def readPort (words : Header D A → ℕ) (r : Slice D A) : Port :=
  ⟨words (.inr (r,.base)),lanes b r,1⟩

/-- The zero-padding command uses the two generated padding columns. -/
def readPadding (words : Header D A → ℕ) (r : Slice D A) : Record :=
  .zero 1 (words (.inr (r,.padWidth))) ⟨words (.inr (r,.padBase)),0,1⟩

/-- Enumerate the fixed rows of one sparse header in public template order. -/
noncomputable def allRows {R : Type*} [Fintype R] (f : R → Record) : List Record :=
  List.ofFn fun i : Fin (Fintype.card R) => f ((Fintype.equivFin R).symm i)

private theorem allRows_valid {R : Type*} [Fintype R] (f : R → Record) (P : Record → Prop) :
    (∀ t ∈ allRows f, P t) ↔ ∀ r, P (f r) := by
  simp only [allRows,List.forall_mem_ofFn_iff]
  constructor
  · intro h r
    simpa using h (Fintype.equivFin R r)
  · exact fun h i => h _

/-- The origin reads one route-free profile header and compares each selector spoke
with its reference spoke. One further row per spoke checks the bank padding. -/
noncomputable def originList (words : Header D A → ℕ) (first : Fin D × Bool) : List Record :=
  originRecords (words (.inl none)) (fun t => words (.inl (some t))) first
    (fun u => readPort b words (.inl u)) ++ allRows (fun u => readPadding words (.inl u))

/-- Each terminal needs one histogram routing record and one zero record per row. -/
noncomputable def terminalList (words : Header D A → ℕ) : List Record :=
  terminalRecord (words (.inl none)) b (fun t => words (.inl (some t))) (readPort b words (.inr (.inl ())))
    (readPort b words (.inr (.inr (.inl ())))) (fun t => readPort b words (.inr (.inr (.inr t)))) ::
      allRows (fun u => readPadding words (.inr u))

/-- The record count at an origin is independent of its matched multiplicity. -/
theorem originList_length (words : Header D A → ℕ) (first : Fin D × Bool) :
    (originList b words first).length = 1+2*Fintype.card (Fin D × Bool) := by
  simp only [originList,originRecords,allRows,List.length_append,List.length_cons,List.length_ofFn]
  omega

/-- Terminal record multiplicity depends only on the alphabet of the paid identity. -/
theorem terminalList_length (words : Header D A → ℕ) : (terminalList b words).length = A+3 := by
  simp [terminalList,allRows]; omega

variable (j : ℕ) (p : Fin A → ℕ)

/-- The compiled public words supply the exact origin ports used by the assignment layout. -/
theorem origin_port (r : Fin D × Bool) :
    readPort b (headerWord b (fun i => i.elim j p)) (.inl r) =
      (originLayout (Fin D × Bool) j A).port r := by
  unfold readPort
  rw [origin_word]
  simp [sliceRead,address,BankLayout.port,lanes,originLayout]

/-- The generated zero record constrains precisely the unused origin suffix. -/
theorem origin_padding (r : Fin D × Bool) :
    readPadding (headerWord b (fun i => i.elim j p)) (.inl r) =
      padding (originLayout (Fin D × Bool) j A) r := by
  unfold readPadding
  rw [origin_word,origin_word]
  rfl

/-- The compiled public words give the exact selector, original, and feeder ports. -/
theorem terminal_port (hp : ∑ a, p a = j) (r : Unit ⊕ Unit ⊕ Fin A) :
    readPort b (headerWord (D := D) b (fun i => i.elim j p)) (.inr r) = (terminalLayout j b p).port r := by
  unfold readPort
  rw [terminal_word b j p hp]
  rcases r with _ | _ | _ <;> simp [sliceRead,address,BankLayout.port,lanes,terminalLayout]

/-- At each terminal the two emitted words constrain precisely the unused suffix. -/
theorem terminal_padding (hp : ∑ a, p a = j) (r : Unit ⊕ Unit ⊕ Fin A) :
    readPadding (headerWord (D := D) b (fun i => i.elim j p)) (.inr r) = padding (terminalLayout j b p) r := by
  unfold readPadding
  rw [terminal_word b j p hp,terminal_word b j p hp]
  rfl

/-- The generated origin records on the padded physical bits test exactly the source
profile's common selector and attained histogram. -/
theorem originList_exact (first : Fin D × Bool) (boxes : List (List Factor))
    (s : (Fin D × Bool) → Fin j → Fin (Nat.clog 2 A) → Fin 2) :
    let L := originLayout (Fin D × Bool) j A
    let bank := paddedBank L (fun u i k => finTwoEquiv (s u i k))
    (∀ r ∈ originList b (headerWord b (fun i => i.elim j p)) first, r.Valid boxes bank) ↔ originTest first p s := by
  intro L bank
  rw [originList,List.forall_mem_append,allRows_valid]
  have hpad (u : Fin D × Bool) : (readPadding (headerWord b (fun i => i.elim j p)) (.inl u)).Valid boxes bank := by
    rw [origin_padding]; exact padded_valid _ _ _ _
  rw [and_iff_left hpad]
  have hports : (fun u => readPort b (headerWord b (fun i => i.elim j p)) (.inl u)) = L.port :=
    funext (origin_port b j p)
  rw [hports]
  change (∀ r ∈ originRecords j p first L.port, r.Valid boxes bank) ↔ _
  rw [origin_records_iff]
  have he : (fun u => selector (A := A) (j := j) bank (L.port u)) = s := by
    funext u i k
    exact (congrArg finTwoEquiv.symm (padded_read L _ u i k)).trans (finTwoEquiv.symm_apply_apply _)
  rw [he]

/-- The generated terminal records check precisely the private order-preserving feeder
routing of the physical profile table. Every padded bit is fixed by the zero rows. -/
theorem terminalList_exact (hp : ∑ a, p a = j) (boxes : List (List Factor))
    (s : Fin j → Fin (Nat.clog 2 A) → Fin 2) (f : ∀ a, Fin (p a) → Fin b → Bool)
    (x : Fin (j*b) → Bool) :
    let L := terminalLayout j b p
    let bank := paddedBank L (terminalData p s f x)
    (∀ r ∈ terminalList b (headerWord (D := D) b (fun i => i.elim j p)), r.Valid boxes bank) ↔ terminalTest p s f x := by
  intro L bank
  rw [terminalList,List.forall_mem_cons,allRows_valid]
  have hpad (r : Unit ⊕ Unit ⊕ Fin A) :
      (readPadding (headerWord (D := D) b (fun i => i.elim j p)) (.inr r)).Valid boxes bank := by
    rw [terminal_padding b j p hp]; exact padded_valid _ _ _ _
  rw [and_iff_left hpad]
  simp only [terminal_port b j p hp]
  change profileValid bank j (L.port (.inl ())) (Nat.clog 2 A) (List.ofFn p)
    (routes A b (L.port (.inr (.inl ()))) (fun a => L.port (.inr (.inr a)))) ↔ _
  rw [terminal_record_iff]
  have hs : selector (A := A) (j := j) bank (L.port (.inl ())) = s := by
    funext i k
    exact (congrArg finTwoEquiv.symm (padded_read L _ (.inl ()) i k)).trans (finTwoEquiv.symm_apply_apply _)
  have hf : feeders (b := b) p bank (fun a => L.port (.inr (.inr a))) = f := by
    funext a i k
    exact padded_read L _ (.inr (.inr a)) i k
  have hx : external (j := j) (b := b) bank (L.port (.inr (.inl ()))) = x := by
    apply blocks.injective
    funext i k
    rw [external,Equiv.apply_symm_apply]
    exact padded_read L _ (.inr (.inl ())) i k
  rw [hs,hf,hx]

end Packing.BankCircuit

end BorderVNP
end Computability
end OAI
