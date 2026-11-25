import OAI.ThreeFlat.Diagonal.AlignedChunkVisit
import OAI.ThreeFlat.Diagonal.HistoryAssembly
import OAI.ThreeFlat.Diagonal.TickInstalledExecution
import OAI.ThreeFlat.Diagonal.TracePreparedSuffix
import OAI.ThreeFlat.RAM.PhysicalPreparedMatrix
import OAI.ThreeFlat.RAM.PhysicalGuardRoute
import OAI.ThreeFlat.RAM.FoldSuffixScale
import OAI.ThreeFlat.Diagonal.TickBucketChronology
import OAI.ThreeFlat.Diagonal.TickLocalMatrix
import OAI.ThreeFlat.Diagonal.NetworkDiagonal

namespace OAI
/-! # The positive chronological matrix at the actual physical endpoints -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel.Buckets

open HistoryContraction TickChronology TickAuxiliary PackedChunkTransfer
open scoped Classical BigOperators
variable {F : Type*} [Field F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {a : ℕ} {c : Clock} {R : GroupRegister P E bits a} {lanes span chunks n t p q d m : ℕ}

/-- The native team identification is required for one time and four bitstrings.
The surrounding template, the shared choices, the complete rotated scans, and
the products of every group and phase are contracted by this theorem. -/
theorem positive_matrix (T : Buckets P bits c a lanes span) (room : ∀ v g,1+R.capacity+2*T.length v g≤a)
    (w : ∀ v g, Aux (T.length v g) → Aux (T.length v g) → ℕ → F)
    (labels : ∀ h, (Fin (bits h) → Bool) ≃ (P.finish h).Boundary)
    (factors : Ext c a → Ext c a → S.Factors F)
    (values : ∀ v (g : Fin c.groups) x y, ((TickRangeChronology.evalTicks c g.val).map
      (w v g.val (T.read v g x) (T.read v g y))).prod =
        ∏ i : {i // T.group v.1 i=g}, P.cells v.1 (factors x y) i.val
          ((P.finish v.1).graph.atVertex (labels v.1 v.2) i.val))
    (N : BitNetwork F p) (order : Fin c.chunks ≃ Bool × Fin chunks)
    (slot : Fin (t+1) → Fin (n+1) → Fin chunks) (active : Fin (t+1) → Bool)
    (pin : Fin (t+1) → Fin (n+1) → Fin q → Aux a → Aux a → Aux a → Aux a → Fin p → Bool)
    (duration : (t+1)*(n+1)=c.last+1) (visited : ∀ (b : Fin (t+1)) (j : Fin (n+1)),
      (active b,slot b j)=order (chunk c (b.val*(n+1)+j.val)))
    (scalar : ∀ (b : Fin (t+1)) (j : Fin (n+1)) x y oa na,
      teamTick N (pin b) j x y oa na=localValue (T.data room w) (b.val*(n+1)+j.val) x y oa na)
    (X : BitNetwork F m) (D : Fin d → Bool)
    (select : Fin (t+1) → Fin m → ApproximatePort (Fin chunks) d n a)
    (keep : Fin (t+1) → Fin chunks → Bool)
    (trace : ∀ x y, S.contract (factors x y) = approximatedMatrix X D select slot active keep
      (TickPhysicalOrder.unpack order x) (TickPhysicalOrder.unpack order y)) :
    templateRun N (List.ofFn id) slot active pin = 1 + approximatedMatrix X D select slot active keep := by
  ext x y
  obtain ⟨x,rfl⟩ := (TickPhysicalOrder.unpack (D:=Aux a) order).surjective x
  obtain ⟨y,rfl⟩ := (TickPhysicalOrder.unpack (D:=Aux a) order).surjective y
  rw [template (T.data room w) N order slot active pin duration visited scalar,
    T.sum room w labels factors values,trace,Matrix.add_apply]
  simp only [Matrix.one_apply,(TickPhysicalOrder.unpack (D:=Aux a) order).injective.eq_iff]

/-- Assemble the positive matrix for the installed tick text and the physical input word order
of the prepared matrix program. The local table values and the cursor forest use identical
terminal boundary labels and paired external endpoint bits. -/
theorem positive_forest {F : Type} [Field F] {S : Shape} {P : Plan F S} {E : P.Codes}
    {bits : P.History→ℕ} {u payload lanes span : ℕ} {c : Clock}
    (s : RAM.PhysicalPinsExpr.Shape) [NeZero s.period]
    {R : GroupRegister P E bits s.bits}
    (T : Buckets P bits c s.bits lanes span)
    (room : ∀ v g,1+R.capacity+2*T.length v g ≤ s.bits)
    (weights : ∀ v g, Aux (T.length v g)→Aux (T.length v g)→ℕ→F)
    (labels : ∀ h, (Fin (bits h)→Bool)≃(P.finish h).Boundary)
    (params : Fin s.parameterBits→Bool) (tick H M : Computability.VPVNP.BurstRAM.PrivateRAM.Machine (16*u^10) u u u)
    (seed : Fin (RAM.FoldSuffixScale.extraSize u)→Bool) (fixed : Fin payload→Bool)
    (N : BitNetwork F ((4*s.bits+(s.teamBits+s.timeBits+s.parameterBits))+s.advice))
    (X : BitNetwork F (s.area+2*s.halfBits))
    (V : Form S (Fin (2*(s.halfBits+s.halfBits))→Bool)) (assembly : P.Assembly V)
    (forest : Forest F V) (size : c.chunks=2*s.chunks)
    (duration : (s.last+1)*(s.inside+1)=c.last+1) :
    let D := RAM.FoldSuffixScale.description tick H M seed fixed s.advice
    let order := AlignedChunks.order (period:=s.period) (width:=s.inside+1) c size
    let load := fun (x y : Bool→Fin s.chunks→Aux s.bits) => TraceBitHeader.endpointPin
      (RAM.PhysicalPinsInput.externalBits x) (RAM.PhysicalPinsInput.externalBits y)
    let eqn := TraceStartupAtScale.fields_size s.advice s.teamBits s.timeBits s.parameterBits s.bits
    (∀ v (g : Fin c.groups) x y, ((TickRangeChronology.evalTicks c g.val).map
      (weights v g.val (T.read v g x) (T.read v g y))).prod =
      ∏ i : {i // T.group v.1 i=g},
        (P.assemble v.1 assembly forest).1.values (P.assemble v.1 assembly forest).2
          (load (TickPhysicalOrder.unpack order x) (TickPhysicalOrder.unpack order y)) i.val
          ((P.finish v.1).graph.atVertex (labels v.1 v.2) i.val)) →
    (∀ (b : Fin (s.last+1)) (j : Fin (s.inside+1)) x y oa na,
      (∏ k : Fin s.teams, N.eval (fun i =>
        (ApproximateImage.tickPins (nt:=s.teamBits) (ns:=s.timeBits) D b.val params j k x y oa na)
          (i.cast eqn))) = localValue (T.data room weights) (b.val*(s.inside+1)+j.val) x y oa na) →
    (∀ x y, (∑ h : P.History, ∑ b : (P.finish h).Boundary, ∏ v,
        (P.assemble h assembly forest).1.values (P.assemble h assembly forest).2 (load x y)
          v ((P.finish h).graph.atVertex b v)) = approximatedMatrix X D
          (fun i => ApproximateImage.select (nt:=s.teamBits) (ns:=s.timeBits) (teams:=s.teams) i.val params) (fun i => s.slots i.val) s.choice s.retained x y) →
    templateRun (cast (congrArg (BitNetwork F) eqn) N) (List.ofFn id)
      (fun i=>s.slots i.val) s.choice (fun i=>ApproximateImage.tickPins (nt:=s.teamBits) (ns:=s.timeBits) (teams:=s.teams) D i.val params) =
      1+approximatedMatrix X D (fun i=>ApproximateImage.select (nt:=s.teamBits) (ns:=s.timeBits) (teams:=s.teams) i.val params)
        (fun i=>s.slots i.val) s.choice s.retained := by
  classical
  intro D order load eqn groups members cursor
  let factors := fun (x y : Ext c s.bits) =>
    V.values forest (load (TickPhysicalOrder.unpack order x) (TickPhysicalOrder.unpack order y))
  refine T.positive_matrix room weights labels factors ?_ (cast (congrArg (BitNetwork F) eqn) N)
    order (fun i => s.slots i.val) s.choice
    (fun i => ApproximateImage.tickPins (nt:=s.teamBits) (ns:=s.timeBits) (teams:=s.teams) D i.val params)
    duration ?_ ?_ X D
    (fun i => ApproximateImage.select (nt:=s.teamBits) (ns:=s.timeBits) (teams:=s.teams) i.val params)
    s.retained ?_
  · intro v g x y
    apply (groups v g x y).trans
    apply Finset.prod_congr rfl
    intro i _
    exact congrFun (congrFun (P.assemble_values v.1 V assembly forest
      (load (TickPhysicalOrder.unpack order x) (TickPhysicalOrder.unpack order y))) i.val)
      ((P.finish v.1).graph.atVertex (labels v.1 v.2) i.val)
  · intro b j
    exact AlignedChunks.visited c size b.val j
  · intro b j x y oa na
    refine Eq.trans ?_ (members b j x y oa na)
    unfold teamTick
    apply Finset.prod_congr rfl
    intro k _
    exact TraceStartupAtScale.eval_cast_arity eqn N
      (ApproximateImage.tickPins (nt:=s.teamBits) (ns:=s.timeBits) D b.val params j k x y oa na)
  · intro x y
    exact (P.contract_eq_networks V assembly forest _).trans (cursor _ _)


end ThreeFlat.Diagonal.TickPhaseModel.Buckets

end
end OAI
