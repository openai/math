import OAI.Computability.BorderVNP.CubePhysicalNativeClaims
import OAI.Computability.BorderVNP.DiagonalTallyAlignedEvaluation

/-! # Common tally claims at the length-only native output address

The runtime descriptor count determines the beginning of the temporary records.
The machine aligns frame word 34 there before running its real allocator. Every
accepting trace therefore checks the same original operand words and forces the
same global broadcast at the length-only entry query address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM
open DiagonalTallyMaterialize (Operand supplied)
open private force_field from OAI.Computability.BorderVNP.DiagonalTallyRAMBroadcast
open private supplied_unchanged from OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun

variable {w : ℕ}

/-- Data in the genuine pre-allocation memory used by the compiled subtotal allocator. -/
structure AlignedAllocationInput (a : Arena) (pub : Arg → Word w) (m : Memory w)
    (os : List Operand) (xs : List (List Bool)) (p : ℕ) : Prop where
  /-- The real source counts, width, team and allocation base. -/
  seed : a.alignedSeed pub m p
  /-- Actual arithmetic and scratch bounds. -/
  fit : a.Fits w (pub 0).val
  /-- The extended-frame fields are addressable. -/
  frameFit : (pub 0).val+101 < 2^w
  /-- Every descriptor has its actual stored coordinate, place and digit words. -/
  operands : supplied m a.fresh p os
  /-- The allocation does not overwrite any operand-source word. -/
  operandsDisjoint : ∀ q, operandReads p os q → outsidePointers (pub 0).val q ∧ q ≠ (pub 0).val+34
  /-- All common-broadcast source bits are preserved by allocation. -/
  broadcastDisjoint : ∀ q, a.raw≤q → q<a.raw+(a.teams*a.dim)*a.width → outsidePointers (pub 0).val q ∧ q ≠ (pub 0).val+34
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

/-- The actual single-pointer write converts all the supplied pre-alignment evidence
into the ordinary allocator's input conditions on its genuine new memory. -/
theorem AlignedAllocationInput.after_align {a : Arena} {pub : Arg → Word w} {m mu : Memory w}
    {os : List Operand} {xs : List (List Bool)} {p : ℕ} (h : AlignedAllocationInput a pub m os xs p)
    (image : readings mu = Function.update (readings m) ((pub 0).val+34) a.fresh) :
    AllocationInput a pub mu os xs p := by
  have keep (j : ℕ) (hj : j ≠ (pub 0).val+34) : mu j = m j := by
    apply Fin.ext
    change readings mu j = readings m j
    rw [image,Function.update_of_ne hj]
  refine ⟨a.seed_after_align pub m mu p h.seed image,h.fit,h.frameFit,?_,
    fun j hj => (h.operandsDisjoint j hj).1,fun j h₁ h₂ => (h.broadcastDisjoint j h₁ h₂).1,
    h.count,h.coords,h.sums,?_,h.number,h.lengths⟩
  · exact supplied_unchanged m mu p a.fresh os h.operands (fun j hj => keep j (h.operandsDisjoint j hj).2)
  · apply DiagonalTallyBits.words_congr m mu a.raw a.width xs h.raw h.lengths
    intro j hlo hhi
    rw [h.number] at hhi
    exact keep j (h.broadcastDisjoint j hlo hhi).2

/-- Every accepting aligned native path checks the row of the actual team's natural
increments. The temporary record pointer comes from this path's true operand count. -/
theorem alignedAllocateAndEvaluate_sound (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : AlignedAllocationInput a pub m os xs p) {es t mt} (run : Runs pub mac alignedAllocateAndEvaluate s m es t mt) :
    ∀ c<a.dim, word w (a.localRow os c) = claimWord a.frame xs a.team c := by
  have room : (pub 0).val+35 < 2^w := (Nat.add_lt_add_left (by decide : 35<101) _).trans h.frameFit
  obtain ⟨_,u,mu,first,_,image,_⟩ := alignTallies_runs pub mac s m _ _ h.seed.2.1 h.seed.2.2.1 room
    (Nat.le_add_left _ _)
  change readings mu = Function.update (readings m) ((pub 0).val+34) (a.fresh+2*a.count-2*a.count) at image
  rw [Nat.add_sub_cancel] at image
  obtain ⟨v,mv,_,_,_,align,tail⟩ := Runs.seq_iff.mp run
  obtain ⟨_,eq,eqm⟩ := align.unique_of_deterministic (by decide) first
  subst v
  subst mv
  exact allocateAndEvaluate_sound a pub mac u mu os xs p (h.after_align image) tail

/-- A shared guess accepted by every actual allocator and subtotal program is exactly
the canonical encoding of their physical natural rows, bit for bit. -/
theorem broadcast_of_aligned_runs {R d width : ℕ} (rows : Fin R → Fin d → ℕ)
    (xs : List (List Bool)) (length : xs.length = R*d) (sizes : ∀ bs∈xs, bs.length = width)
    (widthFit : width ≤ w) (rowFit : ∀ i c, rows i c < 2^width) (arenas : Fin R → Arena)
    (pub : Fin R → Arg → Word w) (mac : Fin R → TeamOpcode.Macros w 8) (state : Fin R → Bank w)
    (mem : Fin R → Memory w) (os : Fin R → List Operand) (ptr : Fin R → ℕ)
    (dim : ∀ i, (arenas i).dim = d) (team : ∀ i, (arenas i).team = i.val)
    (source : ∀ i, AlignedAllocationInput (arenas i) (pub i) (mem i) (os i) xs (ptr i))
    (actual : ∀ i (c : Fin d), (arenas i).localRow (os i) c.val = rows i c)
    (returns : ∀ i, ∃ es t mt, Runs (pub i) (mac i) alignedAllocateAndEvaluate (state i) (mem i) es t mt) :
    xs = broadcast width rows := by
  apply force_field rows widthFit rowFit xs length sizes
  intro i j
  obtain ⟨es,t,mt,run⟩ := returns i
  have h := alignedAllocateAndEvaluate_sound (arenas i) (pub i) (mac i) (state i) (mem i) (os i) xs
    (ptr i) (source i) run j.val (j.isLt.trans_eq (dim i).symm)
  rw [team i,claimWord_fieldWord _ (dim i) xs i j,actual] at h
  exact h.symm

/-- Aligned evaluation and the actual native finish expansion preserve the entire chronological
event tape and final state, including the preliminary frame-pointer update. -/
theorem alignedAllocateAndEvaluate_iff_finish {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} :
    Runs pub mac alignedAllocateAndEvaluate s m es t mt ↔
      Runs pub mac (Evaluator.finishExpansion (.seq alignTallies (.seq allocateTallies prepareTallies))) s m es t mt := by
  constructor
  · intro r
    obtain ⟨_,_,first,_,rfl,align,other⟩ := Runs.seq_iff.mp r
    obtain ⟨_,_,middle,last,rfl,prepare,done⟩ := Runs.seq_iff.mp (allocateAndEvaluate_iff_finish.mp other)
    simpa only [Evaluator.finishExpansion,List.append_assoc] using (align.seq prepare).seq done
  · intro r
    obtain ⟨_,_,_,last,rfl,both,done⟩ := Runs.seq_iff.mp r
    obtain ⟨_,_,first,middle,rfl,align,prepare⟩ := Runs.seq_iff.mp both
    simpa only [alignedAllocateAndEvaluate,List.append_assoc] using align.seq
      (allocateAndEvaluate_iff_finish.mpr (prepare.seq done))

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
