import OAI.Computability.BorderVNP.DiagonalNativeTallyClock
import OAI.Computability.BorderVNP.DiagonalPositiveFinishInput

/-! # Signed tally time and serialized words on every returning shared claim -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalTallyMaterialize DiagonalResidueRAM

/-- A single team's returning aligned program writes the bits of the sum
of the actual claims in the header. Other teams may have guessed arbitrary
rows and the sum is taken at the physical machine word width. -/
theorem aligned_return_claim {w : ℕ} (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (input : AlignedAllocationInput a pub m os xs p) {es t mt}
    (run : Runs pub mac alignedAllocateAndEvaluate s m es t mt) :
    ∀ c<a.dim, ∀ j<w, mt ((a.bitFrame w).dst+(c*w+j)) =
      word w (((∑ i : Fin a.teams,claimWord (w:=w) a.frame xs i.val c).val.testBit j).toNat) := by
  obtain ⟨_,u,mu,align,_,image,_⟩ := alignTallies_runs pub mac s m _ _ input.seed.2.1 input.seed.2.2.1
    (by have := input.frameFit; omega) (Nat.le_add_left _ _)
  change readings mu = Function.update (readings m) ((pub 0).val+34) (a.fresh+2*a.count-2*a.count) at image
  rw [Nat.add_sub_cancel] at image
  have h := input.after_align image
  obtain ⟨v,mv,_,_,_,first,rest⟩ := Runs.seq_iff.mp run
  obtain ⟨_,eq,mem⟩ := first.unique_of_deterministic (by decide) align
  subst v
  subst mv
  obtain ⟨_,q,mq,alloc,_,out,dir,frame,ptr⟩ := allocateTallies_runs a pub mac u mu p h.seed h.fit h.frameFit
  obtain ⟨z,mz,_,_,_,first,ev⟩ := Runs.seq_iff.mp rest
  obtain ⟨_,eq,mem⟩ := first.unique_of_deterministic (by decide) alloc
  subst z
  subst mz
  have source := a.source_after_allocation pub mu mq os xs p h.fit out dir frame ptr h.operands
    h.operandsDisjoint h.broadcastDisjoint h.count h.coords h.sums h.raw h.number h.lengths
  have same := evaluateTallies_sound a pub mac q mq os xs p source ev
  obtain ⟨_,_,_,canonical,_,_,bits⟩ := evaluateTallies_runs a pub mac q mq os xs p source same
  obtain ⟨_,_,rfl⟩ := ev.unique_of_deterministic (by decide) canonical
  exact bits

end DiagonalTallyRAM

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyRAM DiagonalResidueRAM

/-- The real ID and cube-operand writer followed by the signed allocator has a
uniformly charged returning trace, even prior to checking the other teams. Its
serializer always writes the low bits of its own physically asserted column. -/
theorem FinishInput.returned {T dim width w : ℕ} {t : Fin T} {rows : Fin T → Fin dim → ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {state : Bank w} {mem : Memory w}
    {fields : List (List Bool)} (h : FinishInput t rows width pub mac state mem fields)
    (z : Returns (finishExpansion signedOccurrences) pub mac state mem) :
    let a := h.post.arenaFor h.operands.length h.raw dim T t.val width
    traceCost z.val.1 ≤ traceCost h.earlier+(alignTallies.slots+allocateTallies.slots+a.work w h.operands) ∧
      ∀ c : Fin dim, ∀ j<w, z.val.2.2 (h.post.localBase+dim+T*dim+dim+dim+1+(c.val*w+j)) =
        word w (((∑ i : Fin T,claimWord (w:=w) a.frame fields i.val c.val).val.testBit j).toNat) := by
  intro a
  obtain ⟨u,mu,ps,tail,order,first,aligned⟩ := Runs.seq_iff.mp (signedFinish_split.mp z.property)
  obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic (by decide) h.prepare
  have ticks := aligned_return_cost a pub mac h.bank h.selected h.operands fields h.post.descriptors h.allocation aligned
  have bits := aligned_return_claim a pub mac h.bank h.selected h.operands fields h.post.descriptors h.allocation aligned
  refine ⟨?_,fun c j hj => ?_⟩
  · rw [order,show traceCost (h.earlier++tail)=traceCost h.earlier+traceCost tail from VPVNP.RAMBuckets.cost_append ..]
    exact Nat.add_le_add_left ticks _
  · exact (h.post.fixed_outputs h.capacity h.raw dim T t.val width w).2.2.2 ▸ bits c.val c.isLt j hj

end TeamContraction.JointHeader.PositiveFields

end BorderVNP
end Computability
end OAI
