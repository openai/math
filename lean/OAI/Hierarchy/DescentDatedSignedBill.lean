import OAI.Hierarchy.DescentDatedOrdinarySignedInvoice
import OAI.Hierarchy.DescentSignedFeedTariff

namespace OAI
/-! # The ordinary signed successor on the old and new physical host rows -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentParallelBase.ParentFilter DescentSIMDLookup DescentStaticWordColumn DescentDyadicSpan
open FeedBound DescentOrdinarySignedMeta
open ThreeFlat.RAM PhysicalProcedure

private theorem prefix_width (s : SignedExtent) (I : s.Input) (base : ℕ) :
    ((s.jobs I base).map SignedPrefix.Job.width).sum=s.directoryWords+s.peerWords+s.preparation := by
  have writes:=SignedPrefix.width_sum (s.jobs I base) base
  rw [s.finish_jobs I base] at writes
  suffices h : base+((s.jobs I base).map SignedPrefix.Job.width).sum=
      base+(s.directoryWords+s.peerWords+s.preparation) from Nat.add_left_cancel h
  rw [←writes]
  simp only [peerWords,digitArea,preparation,indexWords,oldKey,oldRows,remoteArea,flagArea,
    shapeArea,gateArea,forwardArea,backArea,reverseWords,peerSelectionWords,
    shortPeerKinds,DescentOrdinarySocketPeer.bits,jobsLocal,jobsCompare,slab,
    tailStart,peerHeadOut,peerHeadWords,peerHeadBase,peerHeadRows,DescentOrdinaryCompactPeer.ROM.count,
    peerDirectoryWords,peerLookupWords,peerROMBase,peerKeyBase,peerBits,peerKinds,gateStart,metaStart,
    rawStart,shapesStart,returnedStart,routeStart,backBase,forwardBase,projectedStart,localStart,
    peerStart,ranksStart,lookupStart,lookupWords,keyStart,viewBase,mapBase,mapWords,mapIndices,reverseLookup,reverseBits,DescentOrdinarySignedMeta.stop,
    RawControls.stop,RawControls.width,DescentOrdinarySignedMeta.pageBits,gateWidth,Fused.TablesROM.length,
    DescentOrdinaryDonorSources.PathKeys.endAddress,DescentOrdinaryDonorSources.PathKeys.width,
    DescentOrdinaryDonorSources.ROM.endAddress,DescentOrdinaryDonorSources.ROM.width,directoryWords,
    viewRows,routeTotal,routeBits,forwardBits,finishBits,oldSlab,sockets,requests,compareWidth]
  ring_nf

private theorem prefix_invoices (s : SignedExtent) (I : s.Input) (base K h u : ℕ)
    (parallelism : 0<s.lanes) (width : s.feedUnit≤u) (fit : s.lanes*u≤h/2) :
    let js:=s.jobs I base
    (js.map (SignedPrefix.Job.clocks (s.prepLimit K))).sum≤ s.prefixFactor K*s.feedRows h ∧
    (js.map (SignedPrefix.Job.textSize (s.prepLimit K))).sum≤ s.prefixFactor K*s.feedRows h := by
  intro js
  have real : ∀j∈js,j.pitched := by
    intro j hj
    simp only [js,jobs,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> try trivial
    all_goals exact ⟨span_ge _,Nat.two_pow_pos _⟩
  have physical:=SignedPrefix.budgets js (s.prepLimit K) real
  have count : js.length=21 := rfl
  have live : 1≤ s.feedRows h := by have := Nat.zero_le (2^(h/2)); dsimp [feedRows]; omega
  have page:=s.prefix_paid h u parallelism width fit
  have scanned : js.length+(js.map SignedPrefix.Job.width).sum≤
      (21+(s.rankDirectoryFactor+s.peerInstallFactor+s.preparationFactor))*s.feedRows h := by
    rw [count,prefix_width]
    exact FeedBound.add (constant live 21) page
  have both:=left (20*(s.prepLimit K+1)) scanned
  exact ⟨physical.1.trans both,physical.2.trans both⟩

theorem invoice_words (s : SignedExtent) (I : s.Input) (base K h u : ℕ)
    (parallelism : 0<s.lanes) (width : s.feedUnit≤u) (fit : s.lanes*u≤h/2) :
    s.clockInvoice I base K≤ s.feedClockFactor K*s.feedRows h ∧
    s.textInvoice I base K≤ s.feedTextFactor K*s.feedRows h := by
  let R:=s.feedRows h
  have live : 1≤R:=by have := Nat.zero_le (2^(h/2)); dsimp [R,feedRows]; omega
  have rows : Covers R 1 s.slab:=single (by have := Nat.zero_le (2^(h/2)); dsimp [R,feedRows]; omega)
  have page : 2^(h/2)≤R:=by have := Nat.zero_le (2^(h/2)); dsimp [R,feedRows]; omega
  have bound (x : ℕ) (mem : x∈s.feedExponents) : Covers R 1 (2^x) :=
    single ((Nat.pow_le_pow_right (by decide) ((s.exponent_room parallelism x mem).trans
      ((Nat.mul_le_mul_right s.lanes width).trans (by simpa only [Nat.mul_comm u] using fit)))).trans page)
  have prefixPaid:=s.prefix_invoices I base K h u parallelism width fit
  have dhead : Covers R 28 s.converterLiterals := by
    simpa only [converterLiterals,digitArea,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
      add (left 26 (bound s.compareWidth (by simp [feedExponents])))
        (left 2 (bound (11*s.digitArea) (by simp [feedExponents])))
  have rhead : Covers R 4 s.rankLiterals := by
    have eqn : (s.fieldBits*5+s.fieldBits*5)*s.lanes=10*s.digitArea:=by unfold digitArea;ring
    simpa only [rankLiterals,eqn] using left 4 (bound (10*s.digitArea) (by simp [feedExponents]))
  have mhead : Covers R 32 s.metaLiterals := by
    have eqn : (s.fieldBits*7+s.fieldBits)*s.lanes=8*s.digitArea:=by unfold digitArea;ring
    simpa only [metaLiterals,eqn] using left 32 (bound (8*s.digitArea) (by simp [feedExponents]))
  have shead : Covers R ((8+2*s.cap)*2) s.signedLiterals := by
    have eqn : (s.fieldBits*8+s.fieldBits)*s.lanes=9*s.digitArea:=by unfold digitArea;ring
    simpa only [signedLiterals,eqn,Nat.mul_one] using left ((8+2*s.cap)*2) (bound (9*s.digitArea) (by simp [feedExponents]))
  let fixed:=constant live
  have runRank:=add (fixed 4) (left s.rankColumns (add (fixed 4) (right rows (2*s.rankExpr K+4))))
  have runOut:=add (fixed 4) (left s.outputColumns (add (fixed 4) (right rows (2*s.outputExpr K+4))))
  have textRank:=constant live (s.rankColumns*(11+4*s.rankExpr K))
  have textOut:=constant live (s.outputColumns*(11+4*s.outputExpr K))
  constructor
  · have joined := add prefixPaid.1
      (add (add (add (fixed 8) (left 10 dhead)) (add (add (fixed 4) (left 10 rhead)) runRank))
        (add (add (fixed 4) (left 10 mhead)) (add (add (fixed 4) (left 10 shead)) runOut)))
    simpa only [Covers,clockInvoice,feedClockFactor,rankExpr,outputExpr,rankColumns,outputColumns,converterLiterals,rankLiterals,metaLiterals,signedLiterals,Fused.TablesROM.length, compareWidth, DescentOrdinarySignedParents.ROM.width,
      DescentResetSignedScan.Ranks.headWords, DescentResetSignedScan.Ranks.width, DescentResetSignedScan.Ranks.count,
      DescentNextSignedWindow.Native.All.headWords, DescentNextSignedWindow.Native.All.count,
      DescentNextSignedWindow.Native.All.pageCount, DescentNextSignedWindow.Native.ROM.width,
      DescentResetFieldAssembler.width, Nat.one_mul, Nat.mul_one, Nat.add_assoc] using joined
  · exact add prefixPaid.2 (add
      (add (left 15 (add dhead (fixed 2))) (add (add (left 15 (add rhead (fixed 1))) (fixed 15)) textRank))
      (add (left 15 (add mhead (fixed 1))) (add (add (left 15 (add shead (fixed 1))) (fixed 15)) textOut)))

/-- The bill includes all literal ROM setup, both host populations, both signed scans
and seven times the labels, registers and slots of the actual program. -/
theorem feed_bill (s : SignedExtent) (I : s.Input) (base w K h u ratio : ℕ)
    (snippets : s.SnippetWork I K) (width : s.feedUnit≤u) (pos : 0<u) (wide : 2*u≤h)
    (parallelism : s.lanes=DescentSIMDLookup.lanes h u) (machine : w≤ratio*h) :
    (s.phaseTicks I base w+7*names (s.phase I base w).program)*w≤
      ratio*s.feedFactor K*s.feedVolume h u := by
  have nonzero := (occupancy h u pos wide).1
  have lanesFit := lanes_fit h u
  rw [←parallelism] at nonzero lanesFit
  have quoted := s.invoice_words I base K h u nonzero width lanesFit
  have actual := s.phase_cost I base w K snippets
  have used : s.phaseTicks I base w+7*names (s.phase I base w).program≤ s.feedFactor K*s.feedRows h :=
    add (actual.1.trans quoted.1) (left 7 (actual.2.trans quoted.2))
  calc
    _ ≤ (s.feedFactor K*s.feedRows h)*(ratio*h) := Nat.mul_le_mul used machine
    _ = (ratio*s.feedFactor K)*(s.feedRows h*h) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (s.feed_rows_volume h u pos wide parallelism)

end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
