import OAI.Hierarchy.ProtocolRAMPurchaseMeasured
import OAI.Hierarchy.ProtocolRAMPurchaseCalendarROM
import OAI.Hierarchy.ProtocolRAMPurchaseShelfRecords
import OAI.Hierarchy.ProtocolRAMPurchaseShelfBanks
import OAI.Hierarchy.ProtocolRAMPurchaseSlabFrame
import OAI.Hierarchy.ProtocolRAMFrozenSweep

namespace OAI
/-! # One signed scan in a frozen chronological purchase sweep -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

def stageProgram (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :=
  let c := sh.cfg S depth i
  let t := stage i
  let s := embedded S t c
  let b := sign S t c
  let w := wordBits z d copies
  (PurchaseTape.signedPrefix s b (axis i) w (2^z) (Fintype.card (stageAt z d t).Group) (stageAt z d t).span depth).seq
    (PurchaseStage.dispatch (sh.desc S depth i) w)

def stageClock (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :=
  let c := sh.cfg S depth i
  let t := stage i
  PurchaseTape.signedTicks (embedded S t c) (2^z) (Fintype.card (stageAt z d t).Group) (stageAt z d t).span depth k+
    PurchaseStage.dispatchClock (sh.desc S depth i)

/-- The endpoint scanners read exactly the same trajectory and static socket directory
whose corresponding candidate was accepted or declined by the greedy scan. -/
structure Views (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Mem z d) (i : Key z d k) (m : Mem z d) : Prop where
  flags : ∀ r : Fin (paths z S.degree depth), m (PurchaseStage.decisionBase (sh.desc S depth i)+r.val)=MarkTape.encode (wordBits z d copies)
      ((sh.decisions S π depth phase T kind frozen i)[r.val]'(by simp))
  residual : ∀ r : Fin (2^z),m ((sh.desc S depth i).work+4+r.val)=MarkTape.encode (wordBits z d copies)
    (decide (r∈(advisedPurchases S π (stage i) depth (sh.marked phase T kind frozen i)).2))
  tiles : ProtocolRAMPurchaseGateColumns.TileRows (sh.L S depth i).source (pathRows S π depth i) m
  rom : ∀ a,let L:=sh.L S depth i
    (L.start≤a ∧ a<L.signed.base) ∨ (L.gates.base≤a ∧ a<L.packed) → m a=frozen a

abbrev Untouched (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (frozen m : Mem z d) :=
  ∀ a,(a < sh.firstBase ∨ sh.flagsBase S z d k depth+count z d k*paths z S.degree depth≤a) → m a=frozen a

/-- The geometric columns and the score table are real CPU outputs and immutable
public data at entry. The same frozen bands are read by every later key. -/
structure Incoming (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Mem z d) : Prop where
  dimensions : ∀ i : Key z d k, Ready S (stage i) (sh.cfg S depth i)
  ct : ∀ i : Key z d k, ∃ enc : (stageAt z d (stage i)).Group ↪ Fin (Fintype.card (stageAt z d (stage i)).Group),
    (sh.L S depth i).CTLoaded (banks (stage i)) (advisedStage z d π (stage i)) enc frozen
  table : PurchaseMarks.Table phase T k kind sh.table frozen
  bankEnd : sh.table.base+sh.table.size ≤ sh.firstBase
  stockEnd : ∀ (t : StageAt z d) (j : Fin (2*k)), (sh.stock t j).base+(sh.stock t j).size ≤ sh.firstBase
  afterCT : heapEnd z d copies ≤ sh.firstBase

/-- The four scratch words of the common postprocessor fit immediately below its flags. -/
theorem flags_four (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ)
    (afterCT : heapEnd z d copies ≤ sh.firstBase) : 4 ≤ sh.flagsBase S z d k depth := by
  have n : 1≤extent z d := Nat.two_pow_pos _
  have lower := Nat.mul_le_mul_right 3 n
  have inside := phase_in_heap (h:=z) (copies:=copies) (Nat.zero_le (rounds d))
  simp only [ProbeStage.Native.phase,Nat.zero_mul,Nat.add_zero] at inside
  change 4 ≤ sh.firstBase+count z d k*blockSize z d S.degree depth+2*(paths z S.degree depth+1)
  omega

private theorem read_frozen (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (bank : Bank) {m init : Mem z d}
    (same : sh.Untouched (k:=k) S depth init m) (low : bank.base+bank.size ≤ sh.firstBase) (r : Word _) :
    bank.read m r=bank.read init r := same _ (.inl ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos bank.bits)) _).trans_le low))

abbrev StageEncoding (i : Key z d k) :=
  (stageAt z d (stage i)).Group ↪ Fin (Fintype.card (stageAt z d (stage i)).Group)

/-- Every scratch word left by this stage, including the gate compiler and
mark interpreter temporary words, in the actual runtime group encoding. -/
def stageImage (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (i : Key z d k) (enc : StageEncoding i) (m : Mem z d) : Mem z d :=
  let t:=stage i
  let c:=sh.cfg S depth i
  let tiles:=advisedStage z d π t
  let rows:=PurchaseStage.liveRows tiles enc (portDigits (D:=S.degree) (S.rows (stageAt z d t).span)) depth
  PurchaseStage.dispatchMemory (sh.desc S depth i) rows
    (PurchaseTape.signedOut (embedded S t c) (sign S t c) (axis i) tiles enc depth m)

theorem one_at (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ) (hd : 1≤d)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d) (input : Incoming (k:=k) sh S π depth phase T kind frozen)
    (i : Key z d k) (m : Mem z d) (same : sh.Untouched (k:=k) S depth frozen m) (fresh : sh.Prepared S depth fixture i m)
    (initial : sh.Prepared S depth fixture i frozen)
    (enc : StageEncoding i) (ct : (sh.L S depth i).CTLoaded (banks (stage i)) (advisedStage z d π (stage i)) enc frozen) :
    let out:=sh.stageImage S π depth i enc m
    (sh.stageProgram S depth i).Exec m out (sh.stageClock S depth i) ∧
      sh.Views S π depth phase T kind frozen i out ∧
      ∀ a,(a < sh.lo S depth i ∨ sh.hi S depth i≤a) → out a=m a := by
  let t := stage i
  let j := axis i
  let L := sh.L S depth i
  let c := sh.cfg S depth i
  let s := embedded S t c
  let b := sign S t c
  let g := sh.desc S depth i
  let tiles := advisedStage z d π t
  have size := input.dimensions i
  have keep (f : Fin 3) (r : Word _) := read_frozen sh S depth (stageBank z d (stageNumber t) f) same
    ((stageBank_end z d (stageNumber t) f).trans input.afterCT) r
  have geo : L.CTLoaded (banks t) tiles enc m :=
    ⟨fun r=>(keep 0 _).trans (ct.group r),fun r=>(keep 1 _).trans (ct.input r),fun r=>(keep 2 _).trans (ct.output r)⟩
  have cap := sh.end_le S depth i hd
  have loaded := L.loaded_inside (banks t) tiles enc (S.rows L.sockets) (reverseDigits S L.sockets) fixture m
    (fun a lo hi => fresh a lo (hi.trans_le cap)) size.ct geo size.sockets size.room
  have fits := L.fits (banks t) size.ct size.wide size.degree size.room
  have thresholdEnd : c.threshold.base + c.threshold.size ≤ c.start := size.threshold.2.2
  have thresholdStart : c.threshold.base ≤ c.start := (Nat.le_add_right ..).trans thresholdEnd
  have sFit (a : Fin (2*k)) : (c.stock a).Fits (wordBits z d copies) c.start :=
    ⟨(size.stocks a).2.1, (size.stocks a).2.2.1, (size.stocks a).2.2.2.trans thresholdStart⟩
  have bounds := L.signedFits_of_prefix (banks t) c.threshold c.stock size.directions size.threshold sFit size.room
  have price : PurchaseMarks.Table phase T k kind sh.table m := fun r=>
    (read_frozen sh S depth _ same input.bankEnd r).trans (input.table r)
  have markEq : sh.marked phase T kind m i=sh.marked phase T kind frozen i := by
    have equal (r : Word _) : PurchaseMarks.tested (k:=k) phase T kind sh.table (sh.stock t) m r=
        PurchaseMarks.tested (k:=k) phase T kind sh.table (sh.stock t) frozen r := by
      funext j; simp only [PurchaseMarks.tested,read_frozen sh S depth _ same (input.stockEnd t j)]
    dsimp only [t] at equal
    simp only [marked,PurchaseMarks.stratum,equal]
  let next := portDigits (D:=S.degree) (S.rows (stageAt z d t).span)
  let rows := PurchaseStage.liveRows tiles enc next depth
  let signed := PurchaseTape.signedOut s b j tiles enc depth m
  let out := PurchaseStage.dispatchMemory g rows signed
  obtain ⟨build,words,rom,marks⟩ := PurchaseTape.signed_columns_run s b phase T kind j tiles enc next depth m
    fits bounds loaded price
  have ready := L.dispatchReady (banks t) size.ct size.wide size.degree size.room
  have ⟨binary,wordSet⟩ := PurchaseStage.signed_of_resident g signed ((sh.marked phase T kind m i).map Fin.castSuccEmb) size.wide marks
  rw [markEq] at wordSet
  have ⟨select,residue,flags⟩ := PurchaseStage.dispatch_exec g rows signed ready ⟨words,rom⟩ binary
  have actual := PurchaseStage.measured_advised S π t enc s b depth signed (sh.marked phase T kind frozen i)
    ready ⟨words,rom⟩ binary wordSet
  refine ⟨build.then select,⟨?_,actual.2.2,?_,?_⟩,?_⟩
  · intro r
    have length : g.candidates=paths z S.degree depth := L.candidates_eq
    let index : Fin g.candidates := r.cast length.symm
    have bit := flags index
    rw [wordSet] at bit
    have placement : PurchaseStage.paths g rows=PurchaseTape.paths tiles enc next depth := PurchaseTape.rows_paths ..
    have stable := PurchaseStage.successor_eq tiles enc (Fintype.equivFin (stageAt z d t).Group).toEmbedding next
    have equal : MarkTape.decisions (PurchaseStage.paths g rows)
        ((sh.marked phase T kind frozen i).map Fin.castSuccEmb) = sh.decisions S π depth phase T kind frozen i := by
      rw [placement]
      unfold decisions
      dsimp only
      apply congrArg (fun ps => MarkTape.decisions ps ((sh.marked phase T kind frozen i).map Fin.castSuccEmb))
      unfold PurchaseTape.paths
      exact congrArg (fun succ => (PurchaseDFS.layout (2^z) S.degree depth).map (PurchaseDFS.filled succ))
        (PurchaseStage.successor_eq tiles enc _ next)
    have atIndex (x y : List Bool) (h : x=y) (n : ℕ) (hx : n<x.length) (hy : n<y.length) :
        x[n]=y[n] := by subst y; rfl
    apply bit.trans
    apply congrArg (MarkTape.encode _)
    exact atIndex _ _ equal r.val
      (by simpa only [MarkTape.decisions_length, PurchaseStage.paths, List.length_ofFn, length] using r.isLt)
      (by simpa only [decisions_len] using r.isLt)
  · have held := L.dispatch_rows rows signed words
    have stable := PurchaseStage.successor_eq tiles enc (Fintype.equivFin (stageAt z d t).Group).toEmbedding next
    have rowEq : rows = pathRows S π depth i := by
      simp only [rows,PurchaseStage.liveRows,pathRows,stable,t,tiles,next]
    change ProtocolRAMPurchaseGateColumns.TileRows L.source (pathRows S π depth i) out
    rw [←rowEq]
    exact held
  · intro a
    dsimp only
    intro place
    change (L.start ≤ a ∧ a < L.signed.base) ∨ (L.gates.base ≤ a ∧ a < L.packed) at place
    have static := L.block_static (banks t) sh.table (sh.stock t) j tiles enc rows m a place
    obtain ⟨e₀,e₁,e₂,e₃,e₄,e₅,e₆,e₇,e₈⟩ := L.regions
    have inside : L.start≤a ∧ a<L.endAddress := by rcases place with ⟨l,r⟩|⟨l,r⟩ <;> omega
    exact (static.trans (fresh a inside.1 (inside.2.trans_le cap))).trans
      (initial a inside.1 (inside.2.trans_le cap)).symm
  · intro a outside
    exact L.block_frame (banks t) sh.table (sh.stock t) j tiles enc rows m a (outside.imp_right (cap.trans ·))

theorem one (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ) (hd : 1≤d)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d) (input : Incoming (k:=k) sh S π depth phase T kind frozen)
    (i : Key z d k) (m : Mem z d) (same : sh.Untouched (k:=k) S depth frozen m) (fresh : sh.Prepared S depth fixture i m)
    (initial : sh.Prepared S depth fixture i frozen) :
    ∃ out,(sh.stageProgram S depth i).Exec m out (sh.stageClock S depth i) ∧
      sh.Views S π depth phase T kind frozen i out ∧
      ∀ a,(a < sh.lo S depth i ∨ sh.hi S depth i≤a) → out a=m a := by
  obtain ⟨enc,ct⟩:=input.ct i
  exact ⟨sh.stageImage S π depth i enc m,sh.one_at S π depth hd phase T kind frozen fixture input i m same fresh initial enc ct⟩

theorem views_ext (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (raw : Mem z d) (hd : 1≤d) (i : Key z d k)
    {m m' : Mem z d} (obs : sh.Views S π depth phase T kind raw i m)
    (agree : ∀ a,sh.lo S depth i≤a → a < sh.hi S depth i → m' a=m a) :
    sh.Views S π depth phase T kind raw i m' := by
  let L := sh.L S depth i
  have extent : L.endAddress ≤ sh.hi S depth i := sh.end_le S depth i hd
  obtain ⟨d₀,d₁,d₂,d₃,d₄,d₅,d₆,d₇,d₈⟩ := L.regions
  have count : L.candidates=paths z S.degree depth := L.candidates_eq
  have within : L.start≤L.work := by omega
  constructor
  · intro r
    have ar : sh.lo S depth i≤PurchaseStage.decisionBase (sh.desc S depth i)+r.val ∧
        PurchaseStage.decisionBase (sh.desc S depth i)+r.val < sh.hi S depth i := by
      change L.start≤L.work+4+(L.rows+1)+L.first+r.val ∧ L.work+4+(L.rows+1)+L.first+r.val<_
      have lt : r.val < L.candidates := r.isLt.trans_le count.ge
      omega
    exact (agree _ ar.1 ar.2).trans (obs.1 r)
  · intro r
    have ar : sh.lo S depth i≤(sh.desc S depth i).work+4+r.val ∧
        (sh.desc S depth i).work+4+r.val < sh.hi S depth i := by
      change L.start≤L.work+4+r.val ∧ L.work+4+r.val<_
      have lt : r.val<L.rows := r.isLt;omega
    exact (agree _ ar.1 ar.2).trans (obs.2 r)
  · intro r j
    have pos := L.source_range r j
    exact (agree _ pos.1 (pos.2.trans_le extent)).trans (obs.tiles r j)
  · intro a
    change (L.start ≤ a ∧ a < L.signed.base ∨ L.gates.base ≤ a ∧ a < L.packed) → m' a = raw a
    intro place
    have sub : L.start≤a ∧ a<L.endAddress := by rcases place with ⟨l,r⟩|⟨l,r⟩ <;> omega
    exact (agree _ sub.1 (sub.2.trans_le extent)).trans (obs.rom a place)


end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
