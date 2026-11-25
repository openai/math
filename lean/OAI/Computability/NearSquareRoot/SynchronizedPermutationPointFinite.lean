import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepExecute

/-! # Resource maxima at a fixed physical switch width and reserve -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader.PassPoint
open IntegerMultiplication Code FixedPoint SynchronizedPermutationBudget SynchronizedLayers.ScheduleProgram
open ShortFourier.BatchWord

/-- One width and one reserve identify a finite collection of physical switch calls,
including all admissible row descriptors and every representable record array. -/
abbrev Fiber (k D : ℕ) := {s : Input // s.1.k = k ∧ s.1.D = D}

private abbrev Coordinates (k : ℕ) :=
  (dir : Bool) × Fin (directedPlan (dir,tally k)).length × Bool ×
    Fin (SynchronizedPermutationBudget.width k) × Fin (batches ((CoprimeBox.box k).length/4) k) ×
    (PackedAddress Unit (BoxFin.physicalWidth (box := CoprimeBox.box k)) → Record k)

private def coordinates (s : Input) : Coordinates s.1.k :=
  ⟨s.1.dir,s.1.row,s.1.side,s.1.depth,s.1.batch,s.2⟩

private def encode {k D : ℕ} (s : Fiber k D) : Coordinates k := s.2.1 ▸ coordinates s.1

private theorem encode_injective {k D : ℕ} : Function.Injective (@encode k D) := by
  rintro ⟨⟨⟨kx,Dx,dx,rx,tx,bx,lx,sx,jx,cx⟩,vx⟩,hx,ex⟩
    ⟨⟨⟨ky,Dy,dy,ry,ty,by',ly,sy,jy,cy⟩,vy⟩,hy,ey⟩ eqn
  change kx = k at hx
  change Dx = D at ex
  change ky = k at hy
  change Dy = D at ey
  subst kx
  subst Dx
  subst ky
  subst Dy
  change (⟨dx,rx,sx,jx,cx,vx⟩ : Coordinates k) = ⟨dy,ry,sy,jy,cy,vy⟩ at eqn
  have dirEq := congrArg Sigma.fst eqn
  change dx = dy at dirEq
  subst dy
  have payloadEq := eq_of_heq (Sigma.mk.inj eqn).2
  simp only [Prod.mk.injEq] at payloadEq
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := payloadEq
  rfl

instance finiteFiber (k D : ℕ) : Finite (Fiber k D) := by
  let _ : Finite (Record k) := Finite.of_injective _ (QuadraticAlgebra.equivProd
    (-1 : Dusk.day (componentBits k)) 0).injective
  exact Finite.of_injective _ encode_injective

/-- The reserve is bounded by the physical width on every admissible ticket. -/
instance finiteAtWidth (k : ℕ) : Finite {s : Input // s.1.k = k} := by
  let f (x : {s : Input // s.1.k = k}) : (d : Fin (k+1)) × Fiber k d.val :=
    ⟨⟨x.1.1.D,Nat.lt_succ_of_le (x.1.1.reserve_le.trans_eq x.2)⟩,x.1,x.2,rfl⟩
  exact Finite.of_injective f (fun _ _ e => Subtype.ext (congrArg (fun z => z.2.val) e))

noncomputable local instance (k D : ℕ) : Fintype (Fiber k D) := Fintype.ofFinite _

/-- Maximum for an arbitrary resource measurement on the finite fiber. An empty
fiber contributes zero, so all widths have a defined resource profile. -/
noncomputable def maximumAt (k D : ℕ) (f : Input → ℕ) : ℕ :=
  Finset.univ.sup (fun x : Fiber k D => f x.val)

theorem le_maximumAt (f : Input → ℕ) (x : Input) : f x ≤ maximumAt x.1.k x.1.D f :=
  Finset.le_sup (f := fun z : Fiber x.1.k x.1.D => f z.val) (Finset.mem_univ ⟨x,rfl,rfl⟩)

theorem maximumAt_le (k D : ℕ) (f : Input → ℕ) {top : ℕ}
    (h : ∀ x : Input, x.1.k = k → x.1.D = D → f x ≤ top) : maximumAt k D f ≤ top :=
  Finset.sup_le (fun x _ => h x.1 x.2.1 x.2.2)

end Benes.PackedBatchHeader.PassPoint

end NearSquareRoot
end Computability
end OAI
