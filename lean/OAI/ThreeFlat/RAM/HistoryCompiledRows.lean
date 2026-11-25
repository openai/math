import OAI.ThreeFlat.Diagonal.HistoryAssembly
import OAI.ThreeFlat.RAM.HistoryJoinWords
import OAI.ThreeFlat.RAM.HistoryFactorLibrary

namespace OAI
/-! # Chronological row translation implements the recursive cell network

Each intermediate stream uses four words per trivalent factor, with a tag
in a single shared field-dependent table library. A parent's source stream
is its immediate children's previously generated streams. -/

namespace ThreeFlat.RAM.HistoryCompiledRows

open Diagonal.HistoryContraction BitNetwork.Ordered HistoryJoinScan BitLayout
open scoped BigOperators Classical

variable {F : Type*} {p : ℕ}

/-- One reusable constant field-dependent library, including the stable
compactor gates and the local base coefficients. -/
noncomputable def library [Fintype F] (N : BitNetwork F p) : HistoryFactors.Library N where
  count := Fintype.card ((Fin 3 → Bool) → F)
  id := fun i => Fintype.equivFin _ (N.table i)
  table := (Fintype.equivFin _).symm
  correct := fun _i => ((Fintype.equivFin _).symm_apply_apply _).symm

def metadata (tag : ((Fin 3 → Bool) → F) → ℕ) (N : BitNetwork F p) (i : Fin N.cells) (j : Fin 4) : ℕ :=
  if a : j.val < 3 then sourceAddress (N.source i ⟨j.val,a⟩) else tag (N.table i)

/-- All three source words fit whenever the public and hidden index ranges do. The
fourth word is the actual finite field table identifier. -/
theorem metadata_fits {W:ℕ} (tag : ((Fin 3→Bool)→F)→ℕ) (N:BitNetwork F p)
    (width : 2+p+N.internal≤2^W) (ids : ∀ t,tag t<2^W)
    (i:Fin N.cells) (j:Fin 4) : metadata tag N i j<2^W := by
  unfold metadata
  split
  next ok =>
    cases s:N.source i ⟨j.val,ok⟩ with
    | hidden k => change 2+p+k.val<2^W;have:=k.isLt;omega
    | pin k => change 2+k.val<2^W;have:=k.isLt;omega
    | constant b =>
      cases b with
      | false => change 0<2^W; omega
      | true => change 1<2^W; omega
  next _ => exact ids _

private def mapped {a h p : ℕ} (wire : Fin a → BitSource h p) (j : ℕ) :=
  if hj : j < a then sourceAddress (wire ⟨j,hj⟩) else 0

private theorem mapped_ok {m p h : ℕ} {arity : Fin m → ℕ} (N : (i : Fin m) → BitNetwork F (arity i))
    (wire : (i : Fin m) → Fin (arity i) → BitSource h p) (i : Fin m) (j : Fin (arity i)) :
    mapped (wire i) j.val = sourceAddress (resolve N wire i (.pin j)) := by
  cases z : wire i j <;> simp [mapped,resolve,z,sourceAddress,privateEquiv,j.isLt]

/-- Source addresses in the parent resolve each local public pin through
the same affine or gathered map stored by the selected native job. -/
theorem pin_address {n p h : ℕ} {arity : Fin n→ℕ} (N : ∀ i,BitNetwork F (arity i))
    (wire : ∀ i,Fin (arity i)→BitSource h p) (i : Fin n) (j : Fin (arity i)) :
    sourceAddress (resolve N wire i (.pin j))=sourceAddress (wire i j) := by
  simpa [mapped,j.isLt] using (mapped_ok N wire i j).symm

/-- Recursive interpreter of postorder command words. It uses only the
previous-level stream, the public child pin map and the prefix bit counts. -/
def emitted (tag : ((Fin 3 → Bool) → F) → ℕ) : {p : ℕ} → (T : Tree F p) → Fin T.compile.cells → Fin 4 → ℕ
  | _, .atom N, i, j => metadata tag N i j
  | p, .join h _ arity wire child, i, j =>
    let N := fun a => (child a).compile
    let a : Row N := finSigmaFinEquiv.symm i
    let raw := emitted tag (child a.1) a.2 j
    let off := h + ∑ q : Fin a.1.val, (child (Fin.castLE a.1.isLt.le q)).bits
    if j.val < 3 then translate (arity a.1) p off (mapped (wire a.1)) raw else raw

/-- After any number of joins, all three source addresses and the library
identifier are the actual words of the compiled independent terminal cell. -/
theorem emitted_eq (tag : ((Fin 3 → Bool) → F) → ℕ) (T : Tree F p) (i : Fin T.compile.cells) (j : Fin 4) :
    emitted tag T i j = metadata tag T.compile i j := by
  induction T with
  | atom N => rfl
  | @join p h c arity wire child ih =>
    let N := fun k => (child k).compile
    let z : Row N := finSigmaFinEquiv.symm i
    have index : finSigmaFinEquiv z = i := finSigmaFinEquiv.apply_symm_apply _
    let off := h+∑ q : Fin z.1.val, (child (Fin.castLE z.1.isLt.le q)).bits
    change (if j.val<3 then translate (arity z.1) p off (mapped (wire z.1)) (emitted tag (child z.1) z.2 j)
      else emitted tag (child z.1) z.2 j) = metadata tag (glue N wire) i j
    rw [ih z.1 z.2]
    have shift : off=h+∑ q : Fin z.1.val, (N (Fin.castLE z.1.isLt.le q)).internal := by
      simp only [off,N,Tree.compiled_bits]
    by_cases source : j.val < 3
    · simp only [ite_eq_left source,metadata,dite_eq_left source,shift]
      have row := source_at N wire z ⟨j.val,source⟩
      rw [index] at row
      rw [row]
      exact translate_source N wire z.1 _ (mapped_ok N wire z.1) _
    · simp only [ite_eq_right source,metadata,dite_eq_right source]
      have row := table_at N wire z
      rw [index] at row
      exact congrArg tag row.symm

end ThreeFlat.RAM.HistoryCompiledRows

end OAI
