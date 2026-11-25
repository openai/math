import OAI.Computability.BorderVNP.CubePhysicalAlignedClaims
import OAI.Computability.BorderVNP.DiagonalNativeSignedTags

/-! # Charged time of returning signed tally paths for arbitrary common guesses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA
open DiagonalTallyMaterialize (Operand)
variable {w : ℕ}

/-- A real return forces the local subtotal check, even when the other teams' claims
are arbitrary. Its trace therefore has the measured runtime of the matching local row. -/
theorem allocated_return_cost (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : AllocationInput a pub m os xs p) {es t mt} (run : Runs pub mac allocateAndEvaluate s m es t mt) :
    traceCost es ≤ allocateTallies.slots+a.work w os := by
  obtain ⟨bs,u,mu,first,ha,image,dir,out,ptr⟩ := allocateTallies_runs a pub mac s m p h.seed h.fit h.frameFit
  have source := a.source_after_allocation pub m mu os xs p h.fit image dir out ptr h.operands h.operandsDisjoint
    h.broadcastDisjoint h.count h.coords h.sums h.raw h.number h.lengths
  obtain ⟨v,mv,pre,tail,rfl,alloc,exec⟩ := Runs.seq_iff.mp run
  obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic (by decide) alloc
  have matched := evaluateTallies_sound a pub mac u mu os xs p source exec
  obtain ⟨gs,z,mz,go,hg,_,_⟩ := evaluateTallies_runs a pub mac u mu os xs p source matched
  obtain ⟨eq,_,_⟩ := go.unique_of_deterministic (by decide) exec
  exact (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add ha (eq ▸ hg))

/-- The runtime record-pointer adjustment and both subsequent tally stages meet their actual
work bound on every admitted common prefix. -/
theorem aligned_return_cost (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : AlignedAllocationInput a pub m os xs p) {es t mt} (run : Runs pub mac alignedAllocateAndEvaluate s m es t mt) :
    traceCost es ≤ alignTallies.slots+allocateTallies.slots+a.work w os := by
  have room : (pub 0).val+35 < 2^w := (Nat.add_lt_add_left (by decide : 35<101) _).trans h.frameFit
  obtain ⟨bs,u,mu,first,ha,image,_⟩ := alignTallies_runs pub mac s m _ _ h.seed.2.1 h.seed.2.2.1 room
    (Nat.le_add_left _ _)
  change readings mu = Function.update (readings m) ((pub 0).val+34) (a.fresh+2*a.count-2*a.count) at image
  rw [Nat.add_sub_cancel] at image
  obtain ⟨v,mv,pre,tail,rfl,align,exec⟩ := Runs.seq_iff.mp run
  obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic (by decide) align
  have next := allocated_return_cost a pub mac u mu os xs p (h.after_align image) exec
  rw [show traceCost (bs++tail) = traceCost bs+traceCost tail from VPVNP.RAMBuckets.cost_append ..]
  omega

end DiagonalTallyRAM

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM DiagonalTallyRAM
open DiagonalTallyMaterialize (Operand)
variable {w : ℕ}

/-- The complete actual post-cell stage first resolves packet IDs, then appends the cube
operands, then runs the true aligned allocator and verifier. -/
theorem signedFinish_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es t mt} :
    Runs pub mac (finishExpansion signedOccurrences) s m es t mt ↔
      Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs
        (.seq DiagonalTallyCubeSuffix.appendCubeOperands alignedAllocateAndEvaluate)) s m es t mt := by
  constructor
  · intro run
    obtain ⟨v,mv,pre,tail,rfl,occ,done⟩ := Runs.seq_iff.mp run
    obtain ⟨u,mu,bs,other,rfl,ids,next⟩ := Runs.seq_iff.mp occ
    obtain ⟨z,mz,gs,rest,rfl,app,prepare⟩ := Runs.seq_iff.mp next
    have final := alignedAllocateAndEvaluate_iff_finish.mpr (prepare.seq done)
    simpa only [List.append_assoc] using ids.seq (app.seq final)
  · intro run
    obtain ⟨u,mu,bs,other,rfl,ids,next⟩ := Runs.seq_iff.mp run
    obtain ⟨z,mz,gs,rest,rfl,app,go⟩ := Runs.seq_iff.mp next
    obtain ⟨v,mv,pre,tail,rfl,prepare,done⟩ := Runs.seq_iff.mp (alignedAllocateAndEvaluate_iff_finish.mp go)
    simpa only [finishExpansion,signedOccurrences,Code.block,List.append_assoc] using
      (ids.seq (app.seq prepare)).seq done

/-- Charge every real tally return from the measured ID and cube-operand prefixes and the
actual sparse arena, without assuming a correct common claim from the other teams. -/
theorem signedFinish_cost {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es t mt}
    {ids args : List (TeamRAM.Event w)} {u mu v mv}
    (ident : Runs pub mac DiagonalTallyPacketEmit.producePacketIDs s m ids u mu)
    (append : Runs pub mac DiagonalTallyCubeSuffix.appendCubeOperands u mu args v mv)
    (a : Arena) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (ready : AlignedAllocationInput a pub mv os xs p) (run : Runs pub mac (finishExpansion signedOccurrences) s m es t mt) :
    traceCost es ≤ traceCost ids+traceCost args+alignTallies.slots+allocateTallies.slots+a.work w os := by
  obtain ⟨s₁,m₁,ps,rest,rfl,r₁,tail⟩ := Runs.seq_iff.mp (signedFinish_iff.mp run)
  obtain ⟨rfl,rfl,rfl⟩ := ident.unique_of_deterministic (by decide) r₁
  obtain ⟨s₂,m₂,qs,endTrace,rfl,r₂,go⟩ := Runs.seq_iff.mp tail
  obtain ⟨rfl,rfl,rfl⟩ := append.unique_of_deterministic (by decide) r₂
  have cost := aligned_return_cost a pub mac v mv os xs p ready go
  simp only [traceCost,VPVNP.RAMBuckets.cost_append] at cost ⊢
  omega

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
