import OAI.ThreeFlat.Diagonal.RefreshRecordSource

namespace OAI
/-! # The four actual linked scans produce all retained node records -/

namespace ThreeFlat.Diagonal.RefreshStageNav.Records

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan
open RefreshDemandRows CompressorPacking.Native
open scoped Classical Fin.CommRing
noncomputable section

variable {W v m t d : ℕ} {cur : Word W} {mem : Memory W} {head : ℕ} {P : Pointers} {C : SlotImage.Columns}
    {G : LiftedSlots (Fin v × Fin m) d (BitWord t)} {w : SlotImage.Edge (Fin v × Fin m) (BitWord t) d→ℕ} {read : ℕ→ℕ}

def length (v m t d : ℕ) (q : Table) := v*m*2^t*q.cols d

structure Allocation (W cur head : ℕ) (P : Pointers) (C : SlotImage.Columns) (v m t d : ℕ) : Prop where
  inside : ∀ q,P.dst q+length v m t d q<2^W
  old : ∀ q i,inputs cur head P C v m t d i → apart (P.dst q) (length v m t d q) i
  disjoint : ∀ q r,q≠r → ∀ i,P.dst q≤ i → i<P.dst q+length v m t d q → apart (P.dst r) (length v m t d r) i

def Reads (out : Memory W) (P : Pointers) (head K : ℕ) (G : LiftedSlots (Fin v × Fin m) d (BitWord t))
    (w : SlotImage.Edge (Fin v × Fin m) (BitWord t) d→ℕ) (read : ℕ→ℕ) (q : Table) : Prop :=
  ∀ r,out (P.dst q+(rowOrder d q r).val)=(q.value P head K G w read r:Word W)

theorem Table.publish (s : Data cur mem head P C G w read) (lim : Limits W v m t d P C)
    (alloc : Allocation W cur.val head P C v m t d) (K : ℕ) (q : Table) :
    let out := (q.scan cur m d K).run mem
    Data cur out head P C G w read ∧ Reads out P head K G w read q ∧
    (∀ r,r≠q → Reads mem P head K G w read r → Reads out P head K G w read r) := by
  let res := fun r => (q.value P head K G w read r:Word W)
  let len := length v m t d q
  let dest := P.dst q
  have eqn : (q.scan cur m d K).run mem = fillSegment dest len (tableWord (rowOrder d q) dest res) mem := by
    apply scan_table cur mem (rowOrder d q) res (q.expression cur m d K) q.start (q.start+1) dest
      (by rw [s.pointer]; have := s.header; cases q <;> simp [Table.start] <;> omega)
      (s.table q) (s.span q) (alloc.inside q)
    intro r reg mem' hp fr
    exact q.native (s.frame mem' (fun i hi=>fr i (alloc.old q i hi))) lim K r reg hp
  have outside (i) (hi : apart dest len i) : (q.scan cur m d K).run mem i=mem i := by
    rw [eqn]
    exact segment_other mem _ _ _ _ hi
  refine ⟨s.frame _ (fun i hi=>outside i (alloc.old q i hi)),?_,?_⟩
  · intro r
    rw [eqn]
    exact scan_read mem _ _ _ r
  · intro r ne old row
    rw [outside]
    · exact old row
    · exact alloc.disjoint r q ne _ (Nat.le_add_right _ _) (Nat.add_lt_add_left (rowOrder d r row).isLt _)

theorem records_image (s : Data cur mem head P C G w read) (lim : Limits W v m t d P C)
    (alloc : Allocation W cur.val head P C v m t d) (K : ℕ) :
    let out := (pipeline cur m d K).run mem
    Data cur out head P C G w read ∧ ∀ q, Reads out P head K G w read q := by
  obtain ⟨s1,k,_⟩ := Table.publish s lim alloc K .kernel
  obtain ⟨s2,a,oa⟩ := Table.publish s1 lim alloc K .motif
  obtain ⟨s3,b,ob⟩ := Table.publish s2 lim alloc K .halfHeader
  obtain ⟨s4,c,oc⟩ := Table.publish s3 lim alloc K .halves
  refine ⟨s4,?_⟩
  intro q
  cases q with
  | kernel => exact oc _ (by decide) (ob _ (by decide) (oa _ (by decide) k))
  | motif => exact oc _ (by decide) (ob _ (by decide) a)
  | halfHeader => exact oc _ (by decide) b
  | halves => exact c


end
end ThreeFlat.Diagonal.RefreshStageNav.Records

end OAI
