import OAI.Computability.BorderVNP.CubeScatterPaddingTail
import OAI.Computability.BorderVNP.CubeHostScatterProgram

/-! # Reading the physical crossing bits copied into the host cell banks

The interval scan records the within-bin ordinal of each positive crossing.
The two endpoint cells and the true product labels determine the pair-directory
row. Substituting these actual reads into the host scatter recovers each
corresponding original demand or singleton bit in the supplied cell bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open Physical NativeIntervals HostAddress Crossing Tally VPVNP.MotifBase
open RoutingISA VPVNP.BurstRAM

variable {D m n d blocks b h K s : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
variable {N : Network D P bits} {cell : N.Site → Cell} {il : NativeIntervals.Layout}
variable {before dir mem : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin m ↪o Fin il.count}
variable {cells : Cell ↪ ℕ} {label : Cell → Label (n+1) d} {hz : d^(n+1)=il.alphabet}

/-- Scalar table shape and resident words as read at the start of the host copy.
The two endpoint columns and the width come from the chooser's processed cable
directory. The ordinal comes from the subsequent native interval scan. -/
structure ResidentRows (l : Layout) (il : NativeIntervals.Layout) (before dir mem : ℕ → ℕ)
    (n d blocks b h K s : ℕ) : Prop where
  count : l.count = il.count
  alphabet : l.alphabet = il.alphabet
  endpoints : ∀ (r : Fin il.count), l.cell mem r.val false = il.src before r.val ∧
    l.cell mem r.val true = il.dst before r.val ∧ l.width mem r.val = il.width before r.val
  labels : ∀ (r : Fin il.count) (side : Bool),
    mem (l.labels+l.cell mem r.val side)=before (il.labels+l.cell mem r.val side)
  ordinals : ∀ (r : Fin il.count), mem (l.ordinals+r.val)=dir (il.ordinals+r.val)
  triples : Padding.TripleWords n d blocks l.pairs mem
  bankShape : l.blocks=blocks ∧ l.bc=h*b ∧ l.bankWidth=bankWidth n b h K s ∧ l.selectorWidth=selectorWidth n K h

private theorem ResidentRows.key {l : Layout} (data : ResidentRows l il before dir mem n d blocks b h K s)
    (r : Fin il.count) : l.key mem r.val=il.key before r.val := by
  rw [Layout.key,NativeIntervals.Layout.key,data.labels r false,data.labels r true,
    (data.endpoints r).1,(data.endpoints r).2.1,data.alphabet]

variable {l : Layout}
variable (data : ResidentRows l il before dir mem n d blocks b h K s)
variable (rows : PhysicalRows N cell il before ord row cells label (productCode n d il.alphabet hz))
variable (img : il.Image before il.count dir)
variable (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
  (crossWidth N cell ∘ ord.symm) u ≤ blocks*(h*b))

include rows data in
/-- A positive physical crossing has its genuine endpoints and width in the host's
current RAM, including when other sparse rows denote zero-width cables. -/
theorem ResidentRows.crossing (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    let k := (row (ord e)).val
    l.cell mem k false = cells (crossSrc N cell e) ∧ l.cell mem k true = cells (crossDst N cell e) ∧
      l.width mem k = N.width e.val := by
  intro k
  obtain cols | empty := rows.cable (ord e)
  · rw [ord.symm_apply_apply] at cols
    exact ⟨(data.endpoints _).1.trans cols.1,(data.endpoints _).2.1.trans cols.2.1,(data.endpoints _).2.2.trans cols.2.2⟩
  · have bad := empty.2
    rw [ord.symm_apply_apply] at bad
    change N.width e.val = 0 at bad
    exact ((Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)) bad).elim

include rows data img in
/-- The true native source pointer of a crossing bit equals the original padded
host slot's endpoint address, for either side and either kind of pair. -/
theorem ResidentRows.source_eq (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) (side : Bool) :
    let q := packedSlotEmbedding N cell ord label blocks (h*b) cap ⟨e,j⟩
    l.source mem (row (ord e)).val side j.val =
      address d (n+1) blocks (h*b) l.packets (bankWidth n b h K s) (selectorWidth n K h)
        l.singles (code q.1.1) (code q.1.2) q.2.val side := by
  intro q
  let r := row (ord e)
  have spec := rows.packedSlot img blocks (h*b) cap e j
  change il.key before r.val = pairCode _ q.1 ∧ q.2.val = dir (il.ordinals+r.val)+j.val at spec
  have key : l.key mem r.val=code q.1.1*d^(n+1)+code q.1.2 := by
    rw [data.key r,spec.1]
    change code q.1.1 * il.alphabet + code q.1.2 = _
    rw [← hz]
  have off : mem (l.ordinals+r.val)+j.val=q.2.val := by rw [data.ordinals r,spec.2]
  obtain ⟨kind,first,vertex⟩ := data.triples q.1.1 q.1.2
  obtain ⟨blocksEq,bc,width,sel⟩ := data.bankShape
  change l.source mem r.val side j.val = _
  rw [Layout.source,key,kind,first,vertex,off,blocksEq,bc,width,sel]
  unfold address
  by_cases full : ∀ i < n+1, PairDirectory.digit d (code q.1.1) i ≠ PairDirectory.digit d (code q.1.2) i
  · have yes := (PairDirectory.kind_one_iff ..).mpr full
    simp only [yes,one_ne_zero,ite_false,ite_true,Nat.add_assoc]
  · have no : PairDirectory.kind d (code q.1.1) (code q.1.2) (n+1)=0 := by
      have binary (k : ℕ) : PairDirectory.kind d (code q.1.1) (code q.1.2) k ≤ 1 := by
        induction k with
        | zero => exact le_rfl
        | succ k ih => unfold PairDirectory.kind; split <;> omega
      have neq := mt (PairDirectory.kind_one_iff ..).mp full
      have le := binary (n+1)
      omega
    simp only [no,zero_ne_one,ite_false,ite_true]

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
