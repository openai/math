import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepArguments
import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepFinish
import OAI.Computability.BorderVNP.TransmissionPinsComplete

/-! # Recovering reader words from actual returns and length-only allocation bounds -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ReaderKept

open VPVNP.BurstRAM TeamContraction.ProcessorSlots DiagonalTallyAllocation DiagonalTallyRAM

/-- Any real pin return initiates the four-region preservation theorem, including
when the team has no guesses. The guess is recovered from the physical run. -/
theorem of_pin_return {w : ℕ} (A : StartupArena) (l : Pins.Layout) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (boot : Memory w) (bank : Bank w) (p : Pins.Return pub mac bank boot)
    (frame : Pins.Frame l (readings pub) (readings boot)) (frameFit : readings pub 0+24 < 2^w)
    (teams : 0 < l.teams) (stride : l.stride < 2^w) (count : l.count < 2^w)
    (width : l.width ≤ l.count) (fit : Pins.LoopFits w l)
    (entries pins : ℕ) (packet : entries*w ≤ A.copied) (row : l.ibase=A.ibase) (col : l.hbase=A.hbase) :
    ReaderKept A entries pins boot p.val.2.2 p.val.2.2 := by
  obtain ⟨E,eff⟩ := Pins.preparePins_exact l pub mac boot bank frame frameFit teams stride count width fit
  obtain ⟨bits,rfl⟩ := E.surjective p
  rw [(eff bits).2.2.2.2]
  exact of_prepared A l (Pins.extendGuess bits) boot entries pins packet row col

/-- The actual length-only fragment arena is placed above the reader's full pin
arrays, and the only low indirect store uses the geometric controls. Thus every
return of the linked row emitter and stable bucketer retains the reader image. -/
theorem after_fragment_return {w : ℕ} (A : StartupArena) (entries pins : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w)
    (l : SignedTaskArena.Layout) (ctl u v k : ℕ) :
    let f := FragmentRows.Layout.fromFrame (readings pub 0) (readings m)
    f.Fits w (readings m) → readings m (readings pub 0+92)=ctl →
    (∀ i : Fin 37, readings m (ctl+i.val)=l.controls i.val) → readings pub 0+112 ≤ ctl →
    ctl+37 ≤ l.fragments.quads → f.host.count=l.cube.cables →
    readings m (readings pub 0+9) ≤ l.cube.maxRows → readings m (readings pub 0+11)=l.cube.cells →
    l.endAddress w u v k < 2^w → A.next ≤ l.cube.header.header → A.next ≤ ctl →
    entries*w ≤ A.copied → pins ≤ A.count →
    ∀ {boot pinMem es t mt}, ReaderKept A entries pins boot pinMem m →
      Runs pub mac FragmentRows.emitBucket r m es t mt → ReaderKept A entries pins boot pinMem mt := by
  intro f fit ptr words low below cables raw cells hi placed ctrl packet index boot pinMem es t mt kept run
  obtain ⟨_,_,_,rr,_,_,s,middle,_,first,_,result⟩ := FragmentRows.emitBucket_run pub mac r m l ctl u v k fit ptr words
    low below cables raw cells hi
  obtain ⟨_,rfl,rfl⟩ := run.unique_of_deterministic (by decide) rr
  have all := l.reader_bounds A 0 (pub 0).val 0 ctl placed
  have control : f.control=ctl := ptr
  have quads : f.quads=l.fragments.quads := by
    change readings m (readings m (readings pub 0+92)+28)=l.fragments.quads
    rw [ptr]
    exact words ⟨28,by decide⟩
  apply afterFragments f _ first result kept packet index
  exact ⟨control ▸ ctrl,quads ▸ all.2.2.1,all.2.2.2.1,all.2.2.2.2.1,all.2.2.2.2.2.1⟩

/-- All returns of the complete sparse external compression code preserve the
original reader words, with no condition on their values. -/
theorem after_sparse_return {w : ℕ} (A : StartupArena) (entries pins : ℕ)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {boot pinMem : Memory w} (r : Bank w) (m : Memory w)
    (l : SparseExterior.Layout) (owned : ℕ → SparseExterior.Owned)
    (frame : (pub 0).val=l.frame) (loaded : l.Loaded (readings m))
    (frameFit : l.frame+92 < 2^w) (header : l.control+36 < 2^w)
    (initial : ∀ i < l.count, (owned i).Initial l i m)
    (safe : ∀ i < l.count, ∀ j < i, ∀ a, (owned i).Source l i a → (owned j).Outside l j a)
    (old : ReaderKept A entries pins boot pinMem m) (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (room : A.next ≤ l.compact ∧ A.next ≤ l.tasks ∧ A.next ≤ l.counts)
    {es t mt} (path : Runs pub mac SparseExterior.prepare r m es t mt) :
    ReaderKept A entries pins boot pinMem mt := by
  obtain ⟨_,_,_,canonical,_,image,_⟩ := SparseExterior.prepare_run (pub:=pub) (mac:=mac) r m l owned frame loaded
    frameFit header initial safe
  obtain ⟨_,_,rfl⟩ := path.unique_of_deterministic (by decide) canonical
  exact afterSparse l owned image old packet index room

/-- The genuine signed subtotal suffix uses a reached, count-dependent record
interval, while the reader's original fields lie below the entire reservation
for all legal counts. This uses only the public geometry floor and the occupied
count bound to discharge the two lower-address requirements. -/
theorem after_finish {w : ℕ} (A : StartupArena) (entries pins : ℕ) (l : SignedTaskArena.Layout)
    (raw dim teams team width : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s u : Bank w) (boot pinMem m mu : Memory w) (earlier : List (TeamRAM.Event w))
    (os : List DiagonalTallyMaterialize.Operand) (xs : List (List Bool))
    (prepared : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      s m earlier u mu) (selected : ∀ x < l.after.start, x ≠ (pub 0).val+35 → mu x=m x)
    (input : AlignedAllocationInput (l.after.arenaFor os.length raw dim teams team width) pub mu os xs l.after.descriptors)
    {es t mt} (run : Runs pub mac (Evaluator.finishExpansion Evaluator.signedOccurrences) s m es t mt)
    (frame : (pub 0).val=A.frame) (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (placement : A.next ≤ l.cube.header.header) (capacity : os.length ≤ l.after.bound.operands)
    (before : ReaderKept A entries pins boot pinMem m) : ReaderKept A entries pins boot pinMem mt := by
  have bounds := l.reader_bounds A team (pub 0).val 0 0 placement
  have reserve : l.after.start ≤ l.after.fresh := by rw [l.after.footprint]; omega
  have fit := l.after.arena_lower capacity raw dim teams team width
  exact signedFinish_readerKept A entries pins pub mac _ s u boot pinMem m mu earlier os xs _ l.after.start
    prepared selected input run frame packet index ⟨by omega,by omega⟩ before

end RoutingISA.ReaderKept

end BorderVNP
end Computability
end OAI
