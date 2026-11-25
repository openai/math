import OAI.Computability.BorderVNP.CubePhysicalNativeTally
import OAI.Computability.BorderVNP.DiagonalNativeExpansionValue

/-! # A common subtotal broadcast is forced by the actual allocated native team paths

The data conditions describe the RAM before allocation. Every returning native path reads
the words and claims of that original memory. Once the physical team rows have passed,
there is only one possible common subtotal broadcast; the post-call continuation uses the
same event trace and final state as the actual allocated tally instructions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM
open DiagonalTallyMaterialize (Operand supplied)
open private force_field from OAI.Computability.BorderVNP.DiagonalTallyRAMBroadcast

variable {w : ℕ}

/-- Data in the genuine pre-allocation memory used by the compiled subtotal allocator. -/
structure AllocationInput (a : Arena) (pub : Arg → Word w) (m : Memory w)
    (os : List Operand) (xs : List (List Bool)) (p : ℕ) : Prop where
  /-- The real source counts, width, team and allocation base. -/
  seed : a.seed pub m p
  /-- Actual arithmetic and scratch bounds. -/
  fit : a.Fits w (pub 0).val
  /-- The extended-frame fields are addressable. -/
  frameFit : (pub 0).val+101 < 2^w
  /-- Every descriptor has its actual stored coordinate, place and digit words. -/
  operands : supplied m a.fresh p os
  /-- The allocation does not overwrite any operand-source word. -/
  operandsDisjoint : ∀ q, operandReads p os q → outsidePointers (pub 0).val q
  /-- All common-broadcast source bits are preserved by allocation. -/
  broadcastDisjoint : ∀ q, a.raw≤q → q<a.raw+(a.teams*a.dim)*a.width → outsidePointers (pub 0).val q
  /-- The physical descriptor count matches its list. -/
  count : os.length = a.count
  /-- Each coordinate is in the tally array. -/
  coords : ∀ o∈os, o.pair.1 < a.dim
  /-- All local integer increments fit the machine words. -/
  sums : ∀ c<a.dim, a.localRow os c < 2^w
  /-- The common fields are actual words of the allocated input tape. -/
  raw : DiagonalTallyBits.WordsAt m a.raw xs
  /-- There is one field for every team and coordinate. -/
  number : xs.length = a.teams*a.dim
  /-- Each broadcast field has the chosen bit width. -/
  lengths : ∀ bs∈xs, bs.length = a.width

/-- Converse for the entire allocator followed by its true tally evaluator. This
forces the caller's row even when the common broadcast is an arbitrary guess. -/
theorem allocateAndEvaluate_sound (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : AllocationInput a pub m os xs p) {es t mt} (run : Runs pub mac allocateAndEvaluate s m es t mt) :
    ∀ c<a.dim, word w (a.localRow os c) = claimWord a.frame xs a.team c := by
  obtain ⟨bs,u,mu,first,_,image,dir,out,ptr⟩ := allocateTallies_runs a pub mac s m p h.seed h.fit h.frameFit
  obtain ⟨v,mv,_,_,_,alloc,tail⟩ := Runs.seq_iff.mp run
  obtain ⟨_,eq,eqm⟩ := alloc.unique_of_deterministic (by decide) first
  subst v
  subst mv
  exact evaluateTallies_sound a pub mac u mu os xs p
    (a.source_after_allocation pub m mu os xs p h.fit image dir out ptr h.operands h.operandsDisjoint
      h.broadcastDisjoint h.count h.coords h.sums h.raw h.number h.lengths) tail

/-- A shared guess accepted by every actual allocator and subtotal program is exactly
the canonical encoding of their physical natural rows, bit for bit. -/
theorem broadcast_of_allocated_runs {R d width : ℕ} (rows : Fin R → Fin d → ℕ)
    (xs : List (List Bool)) (length : xs.length = R*d) (sizes : ∀ bs∈xs, bs.length = width)
    (widthFit : width ≤ w) (rowFit : ∀ i c, rows i c < 2^width) (arenas : Fin R → Arena)
    (pub : Fin R → Arg → Word w) (mac : Fin R → TeamOpcode.Macros w 8) (state : Fin R → Bank w)
    (mem : Fin R → Memory w) (os : Fin R → List Operand) (ptr : Fin R → ℕ)
    (dim : ∀ i, (arenas i).dim = d) (team : ∀ i, (arenas i).team = i.val)
    (source : ∀ i, AllocationInput (arenas i) (pub i) (mem i) (os i) xs (ptr i))
    (actual : ∀ i (c : Fin d), (arenas i).localRow (os i) c.val = rows i c)
    (returns : ∀ i, ∃ es t mt, Runs (pub i) (mac i) allocateAndEvaluate (state i) (mem i) es t mt) :
    xs = broadcast width rows := by
  apply force_field rows widthFit rowFit xs length sizes
  intro i j
  obtain ⟨es,t,mt,run⟩ := returns i
  have h := allocateAndEvaluate_sound (arenas i) (pub i) (mac i) (state i) (mem i) (os i) xs
    (ptr i) (source i) run j.val (j.isLt.trans_eq (dim i).symm)
  rw [team i,claimWord_fieldWord _ (dim i) xs i j,actual] at h
  exact h.symm

/-- The allocator, materializer, clear and subtotal completion are exactly the same
chronological instructions as the native evaluator's post-call continuation. -/
theorem allocateAndEvaluate_iff_finish {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} :
    Runs pub mac allocateAndEvaluate s m es t mt ↔
      Runs pub mac (Evaluator.finishExpansion (.seq allocateTallies prepareTallies)) s m es t mt := by
  constructor
  · intro r
    obtain ⟨_,_,xs,_,rfl,first,tail⟩ := Runs.seq_iff.mp r
    obtain ⟨_,_,ys,zs,rfl,second,last⟩ := Runs.seq_iff.mp tail
    simpa only [Evaluator.finishExpansion,List.append_assoc] using (first.seq second).seq last
  · intro r
    obtain ⟨_,_,_,zs,rfl,both,last⟩ := Runs.seq_iff.mp r
    obtain ⟨_,_,xs,ys,rfl,first,second⟩ := Runs.seq_iff.mp both
    simpa only [allocateAndEvaluate,evaluateTallies,List.append_assoc] using first.seq (second.seq last)

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
