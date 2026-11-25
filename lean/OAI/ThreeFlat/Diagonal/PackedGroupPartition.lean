import OAI.ThreeFlat.Diagonal.PackedBucketTransfer

namespace OAI
/-! # Reindexing the complete external bit array by its physical owner -/

namespace ThreeFlat.Diagonal.PackedGroupPartition

open PackedChunkTransfer HistoryContraction TickChronology
open scoped Classical BigOperators
noncomputable section

variable {I : Type*} {a C : ℕ} (owner : Fin C × Fin a → I) (q : I → Fin C → Fin a → ℕ)
  (hit : ∀ g z, q g z.1 z.2 ≠ 0 ↔ owner z = g) {n : I → ℕ} (e : ∀ g, Live (q g) ≃ Fin (n g))

def fiber (g : I) : {z // owner z=g} ≃ Fin (n g) :=
  (Equiv.subtypeEquivRight (fun z => (hit g z).symm)).trans (e g)

def index : (Fin C → Fin a → Bool) ≃ ∀ g, Fin (n g) → Bool :=
  (Equiv.curry _ _ _).symm.trans (Equiv.piCongrFiberwise (f:=owner)
    (fun g => (fiber owner q hit e g).arrowCongr (Equiv.refl Bool)))

theorem index_apply (x : Fin C → Fin a → Bool) (g : I) :
    index owner q hit e x g = project (q g) (e g) x := rfl

theorem read (g : I) (x : Fin C → Fin a → Bool) (z : Live (q g)) :
    index owner q hit e x g (e g z) = x z.val.1 z.val.2 := by
  rw [index_apply]
  simp [project]

theorem outside (g : I) (x y : Fin C → Fin a → Bool) :
    holdsOutside (q g) x y ↔ ∀ j, j≠g → index owner q hit e x j=index owner q hit e y j := by
  constructor
  · intro kept j ne
    funext k
    let z := (e j).symm k
    have own := (hit j z.val).mp z.property
    have skip : q g z.val.1 z.val.2 = 0 := by
      by_contra active
      exact ne (own.symm.trans ((hit g z.val).mp active))
    exact kept z.val.1 z.val.2 skip
  · intro kept i j h
    let z : Live (q (owner (i,j))) := ⟨(i,j),(hit _ _).mpr rfl⟩
    have ne : owner (i,j) ≠ g := fun eq => (hit _ _).mpr eq h
    have eq := congrFun (kept _ ne) (e _ z)
    simpa only [read] using eq

theorem kernel {F : Type*} [CommSemiring F] [Fintype I] [DecidableEq I]
    (K : ∀ g, Matrix (Fin (n g) → Bool) (Fin (n g) → Bool) F) (g : I) :
    ((chunkKernel K {g}).submatrix (index owner q hit e) (index owner q hit e)) =
    (fun x y => if holdsOutside (q g) x y then K g (project (q g) (e g) x) (project (q g) (e g) y) else 0) := by
  ext x y
  simp only [Matrix.submatrix_apply,chunkKernel,Finset.mem_singleton,Finset.prod_singleton,
    outside owner q hit e,index_apply]

/-- The interval containing an external address identifies its unique group even when
the native bucket-row list and the physical scan have different orders. -/
theorem bucket_hit {F : Type*} [CommSemiring F] {S : Shape} (P : Plan F S) (h : P.History)
    {groups : ℕ} (grp : (P.finish h).Site → Fin groups) (bs : List (Bucket S.Site))
    (c : Clock) (own : Fin c.chunks × Fin a → Fin groups)
    (covers : ∀ z : Fin c.chunks × Fin a, ∃ b∈bs, b.lo ≤ z.1.val*a+z.2.val ∧ z.1.val*a+z.2.val < b.hi)
    (agrees : ∀ z : Fin c.chunks × Fin a, ∀ b∈bs, b.lo ≤ z.1.val*a+z.2.val →
      z.1.val*a+z.2.val < b.hi → grp (P.destination h b.site)=own z) :
    ∀ (g : Fin groups) (z : Fin c.chunks × Fin a),
      RotatedBucketScan.code P h (fun i => (grp i).val) bs c g.val a z.1 z.2 ≠ 0 ↔ own z=g := by
  intro g z
  unfold RotatedBucketScan.code
  rw [BucketIntervalCodes.plan_rows]
  constructor
  · intro nonzero
    by_contra ne
    apply nonzero
    apply (BucketIntervalCodes.code_zero_iff ..).mpr
    rintro b hb ⟨eq,lo,hi⟩
    exact ne ((agrees z b hb lo hi).symm.trans (Fin.ext eq))
  · intro ownEq zero
    obtain ⟨b,hb,lo,hi⟩ := covers z
    exact (BucketIntervalCodes.code_zero_iff ..).mp zero b hb ⟨congrArg Fin.val ((agrees z b hb lo hi).trans ownEq),lo,hi⟩

end
end ThreeFlat.Diagonal.PackedGroupPartition

end OAI
