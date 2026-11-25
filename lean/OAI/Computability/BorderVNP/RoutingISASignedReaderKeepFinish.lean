import OAI.Computability.BorderVNP.RoutingISASignedReaderKeep
import OAI.Computability.BorderVNP.DiagonalTallySignedFinish

/-! # Reader fields survive the full aligned native subtotal calculation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyMaterialize
open private total_outside scatter_outside from OAI.Computability.BorderVNP.DiagonalTallyRAMLayout
open private serializeSetup_runs from OAI.Computability.BorderVNP.DiagonalTallyRAMSerialize
open private Arena.prepare_runs from OAI.Computability.BorderVNP.DiagonalTallyRAMEvaluation

variable {w : ℕ}

private theorem serialize_before (dst : ℕ) (bits : ℕ → Bool) (m : Memory w) (i n x : ℕ) (low : x<dst) :
    DiagonalTallyUnpack.writeSlice dst bits m i n x=m x := by
  induction n generalizing m i with
  | zero => rfl
  | succ n ih => rw [DiagonalTallyUnpack.writeSlice,ih,Function.update_of_ne (by omega)]

/-- Materialization and all four tally passes preserve the whole lower region
of the genuine dynamic tally allocation, even on an arbitrary accepting claim. -/
theorem evaluateTallies_before_fresh (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : a.Source pub m os xs p) {es t mt} (run : Runs pub mac evaluateTallies s m es t mt) {x : ℕ}
    (low : x<a.fresh) : mt x=m x := by
  obtain ⟨u,mu,_,_,_,prepared,comp⟩ := Runs.seq_iff.mp run
  obtain ⟨_,v,prep,_⟩ := Arena.prepare_runs a pub mac s m os xs p h
  obtain ⟨_,rfl,rfl⟩ := prepared.unique_of_deterministic (by decide) prep
  let initial := a.initialized m os
  let g := a.bitFrame w
  let rs := os.map Operand.pair
  have hi := a.input pub m os xs p h.fits h.directory h.operands h.count h.coords h.sums h.raw h.number h.lengths
  have matched := complete_sound pub mac u initial a.frame rs xs hi comp
  obtain ⟨_,v,st,_,_⟩ := stage_runs pub mac u initial a.frame rs xs hi matched
  obtain ⟨v',mv,_,_,_,first,rest⟩ := Runs.seq_iff.mp comp
  obtain ⟨_,rfl,rfl⟩ := first.unique_of_deterministic (by decide) st
  let bank := resultBank a.frame rs xs initial
  have dir := a.finalFrame pub m os xs h.fits h.bitsDirectory hi
  have span := h.fits.dir
  have bound : (pub 0).val+43 < 2^w := by
    have z : a.fresh+2*a.count<2^w := h.fits.frameFit.2.2.1
    omega
  obtain ⟨_,q,load,_,hl,zero⟩ := serializeSetup_runs pub mac v' bank g a.dim dir h.fits.bitFit bound
  obtain ⟨_,z,unpacked,_,_,_⟩ := DiagonalTallyUnpack.unpack_runs pub mac g q bank 0 g.total h.fits.bitFit hl zero (Nat.zero_add _)
  obtain ⟨_,_,hm⟩ := rest.unique_of_deterministic (by decide) (load.seq unpacked)
  rw [hm,serialize_before]
  · change resultBank a.frame rs xs initial x = m x
    have l : x < a.frame.localBase := by change x < a.fresh+2*a.count; omega
    have c : x < a.frame.claims := by change x < a.fresh+2*a.count+a.dim; omega
    have t : x < a.frame.totals := by change x < a.fresh+2*a.count+a.dim+a.teams*a.dim+a.dim; omega
    rw [resultBank,total_outside _ _ _ _ _ _ (Or.inl (by simpa only [Nat.add_zero] using t)),
      DiagonalTallyBits.outputMemory_outside _ _ _ _ (Or.inl c),
      scatter_outside initial a.frame.localBase a.frame.dim x rs hi.coords (Or.inl l)]
    exact a.initialized_before m os x low
  · change x < a.fresh+2*a.count+a.dim+a.teams*a.dim+a.dim+a.dim+1; omega

/-- The dynamic aligner and allocator touch only their dedicated directory
words before the tally arena. The complete accepting suffix keeps every
other earlier word. -/
theorem aligned_before_fresh (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : AlignedAllocationInput a pub m os xs p) {es t mt} (run : Runs pub mac alignedAllocateAndEvaluate s m es t mt)
    {x : ℕ} (low : x<a.fresh) (away : outsidePointers (pub 0).val x) (ptr : x ≠ (pub 0).val+34) :
    mt x=m x := by
  obtain ⟨v,mv,_,_,_,align,tail⟩ := Runs.seq_iff.mp run
  obtain ⟨_,u,mu,first,_,image,_⟩ := alignTallies_runs pub mac s m _ _ h.seed.2.1 h.seed.2.2.1
    (by have := h.frameFit; omega) (Nat.le_add_left _ _)
  obtain ⟨_,rfl,rfl⟩ := align.unique_of_deterministic (by decide) first
  change readings mv=Function.update (readings m) ((pub 0).val+34) (a.fresh+2*a.count-2*a.count) at image
  rw [Nat.add_sub_cancel] at image
  have src := h.after_align image
  obtain ⟨q,mq,_,_,_,alloc,rest⟩ := Runs.seq_iff.mp tail
  obtain ⟨_,_,_,install,_,mem,dir,out,op⟩ := allocateTallies_runs a pub mac v mv p src.seed src.fit src.frameFit
  obtain ⟨_,rfl,rfl⟩ := alloc.unique_of_deterministic (by decide) install
  have data := a.source_after_allocation pub mv mq os xs p src.fit mem dir out op src.operands src.operandsDisjoint
    src.broadcastDisjoint src.count src.coords src.sums src.raw src.number src.lengths
  rw [evaluateTallies_before_fresh a pub mac q mq os xs p data rest low]
  apply Fin.ext
  change readings mq x = readings m x
  rw [mem,a.installed_outside _ _ _ _ away,image,Function.update_of_ne ptr]

/-- The selected-ID producer preserves all earlier words except its dynamic count.
Combined with aligned allocation and serialization, the actual signed suffix
preserves each of the four reader regions. -/
theorem signedFinish_readerKept (A : TeamContraction.ProcessorSlots.StartupArena)
    (entries pins : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (a : Arena) (s u : Bank w) (boot pinMem m mu : Memory w) (earlier : List (TeamRAM.Event w))
    (os : List Operand) (xs : List (List Bool)) (p cut : ℕ)
    (first : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      s m earlier u mu) (selected : ∀ x < cut, x ≠ (pub 0).val+35 → mu x=m x)
    (input : AlignedAllocationInput a pub mu os xs p) {es t mt}
    (run : Runs pub mac (Evaluator.finishExpansion Evaluator.signedOccurrences) s m es t mt)
    (frame : (pub 0).val=A.frame) (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (safe : A.next ≤ cut ∧ A.next ≤ a.fresh) (before : ReaderKept A entries pins boot pinMem m) :
    ReaderKept A entries pins boot pinMem mt := by
  obtain ⟨q,mq,_,_,_,r,tail⟩ := Runs.seq_iff.mp (signedFinish_split.mp run)
  obtain ⟨_,rfl,rfl⟩ := r.unique_of_deterministic (by decide) first
  apply before.advance
  intro x hx
  have lo := hx.below packet index
  have ne (k : ℕ) (hk : k < 112) (other : k ∉ readerControls) : x ≠ (pub 0).val+k :=
    frame ▸ hx.ne_field hk other
  exact (aligned_before_fresh a pub mac q mq os xs p input tail (lo.trans_le safe.2)
    ⟨ne 32 (by decide) (by decide),ne 37 (by decide) (by decide),ne 41 (by decide) (by decide),
     ne 42 (by decide) (by decide),ne 43 (by decide) (by decide)⟩ (ne 34 (by decide) (by decide))).trans
    (selected _ (lo.trans_le safe.1) (ne 35 (by decide) (by decide)))

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
