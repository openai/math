import OAI.Hierarchy.GridPinHeaderSource
import OAI.Hierarchy.GridPinArenaSlices
import OAI.Hierarchy.GridPinBankRoom

namespace OAI
/-! # Physical bank windows for a calibrated pin publisher -/

namespace Hierarchy.GridPinArena

open GridPinPublisher

/-- A complete allocator subwindow is available at each base, even when the
native pass visits only an initial part of its bank. -/
structure Windows (W : ℕ) (P : Plan) (g : ℕ) : Prop where
  fit : ∀ b : Bank, b.base P+g < 2^W
  disjoint : ∀ b c : Bank, b≠c → b.base P+g≤c.base P ∨ c.base P+g≤b.base P

theorem Windows.ne {W g : ℕ} {P : Plan} (win : Windows W P g) (b c : Bank)
    (different : b≠c) {i j : ℕ} (hi : i<g) (hj : j<g) : b.base P+i≠c.base P+j := by
  have := win.disjoint b c different
  omega

/-- Footprints of the actual arithmetic scans at the chosen word age. -/
structure Small (w : ℕ) (P : Plan) (bitCount laneCount staged K : ℕ) : Prop where
  ticksPos : 0<P.ticks
  pinsPos : 0<P.header.pins
  spanPos : 0<P.source.span
  pinStorage : P.ticks*P.header.pins≤ slab w
  factors : P.factors≤ slab w
  resource : P.factor.items*P.factor.stride≤ slab w
  classes : K≤ slab w
  selector : P.header.selector≤ slab w
  bits : bitCount≤ slab w
  full : laneCount≤ slab w
  staged : staged≤ slab w
  span : P.source.span≤ slab w
  capacity : bitCount≤laneCount*P.source.span

/-- Numerical premises of the header, factor, bucket, and scatter scans.
The witnesses for the values read from memory remain in their native procedures. -/
structure Scalars (W : ℕ) (P : Plan) (bits full K g : ℕ) : Prop where
  bank : BankRoom W P bits full
  window : Windows W P g
  wordPos : 0<W
  two : 2<2^W
  ticksPos : 0<P.ticks
  pinsPos : 0<P.header.pins
  spanPos : 0<P.source.span
  ticksFit : P.ticks<2^W
  factorsFit : P.factors<2^W
  lanesFit : P.lanes<2^W
  literalsFit : P.literals<2^W
  endsFit : P.endpoints<2^W
  pinsFit : P.header.pins<2^W
  outFit : P.header.literalBase+P.ticks*P.header.pins<2^W
  textFit : P.header.textBase+P.header.text<2^W
  opsFit : P.header.operandBase+P.header.operandBits<2^W
  selFit : P.header.selectorBase+P.header.selector<2^W
  separate : ∀ z, GridPinHeaderNative.source P.header z →
    z<P.header.literalBase ∨ P.header.literalBase+P.ticks*P.header.pins≤z
  itemsFit : P.factor.items<2^W
  classesFit : K<2^W
  spanFit : P.source.span<2^W
  bitsFit : bits<2^W
  fullFit : full<2^W
  within : P.lanes≤full
  active : ∀ i<P.lanes, i*P.bucket.span≤P.bucket.cap
  bitFit : P.source.external+P.literals≤bits

private def address (J g staged : ℕ) : Bank→ℕ
  | .raw => 0
  | .selector => 12*J
  | .keys => 15*J+g
  | .owners => 15*J+3*g
  | .resource => 14*J
  | .ancestors => 16*J+g+staged
  | .ticks => 15*J+8*g
  | .factors => 15*J+9*g
  | .blocks => 15*J+10*g
  | .rails => 15*J+11*g
  | .dest => 9*J
  | .literals => 10*J

set_option maxHeartbeats 2000000 in
private theorem windows_of_address {W J g staged : ℕ} (P : Plan) (loc : 32*g≤J)
    (word : 32*J<2^W) (depth : staged≤g)
    (base : ∀ b : Bank, b.base P=address J g staged b) : Windows W P g := by
  constructor
  · intro b
    rw [base]
    cases b <;> simp only [address] <;> omega
  · intro b c different
    rw [base b,base c]
    cases b <;> cases c <;> simp only [address] <;> first | exact False.elim (different rfl) | omega

variable (w k n q pins nparams sel text compact rails bits N stages full span : ℕ)
local notation "P" => canonical w k n q pins nparams sel text compact rails bits N stages full span
local notation "K" => (20*(w+1)+2)^(k+2)

private theorem within_of_capacity (bits full span : ℕ) (pos : 0< span) (cap : bits≤full*span) :
    (bits+span-1)/span ≤ full := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul pos).mpr
  rw [Nat.succ_mul]
  omega

private theorem active_of_lt (bits span i : ℕ) (pos : 0< span) (hi : i<(bits+span-1)/span) :
    i*span≤bits := by
  have room := (Nat.le_div_iff_mul_le pos).mp (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at room
  omega

/-- All room and separation assertions hold for the canonical physical
publisher, its stored factor classes, and the final relocated owner archive. -/
theorem canonical_scalars (pos : 0<w)
    (small : Small w P bits full (stages*full) K)
    (raw : GridSelfHeader.rawSize w rails compact nparams≤bits) (code : text≤w^2) :
    Scalars (64*w) P bits full K (slab w) := by
  let J := GridDescription.sector w
  let g := slab w
  obtain ⟨loc,word⟩ := scales w pos
  change 32*g≤J at loc
  change 32*J<2^(64*w) at word
  have base (b : Bank) : b.base P=address J g (stages*full) b := by cases b <;> rfl
  have win := windows_of_address P loc word small.staged base
  have smallWord : g<2^(64*w) := by omega
  have gPos : 0<g := Nat.two_pow_pos _
  have ticks : (P).ticks ≤ g :=
    (Nat.le_mul_of_pos_right _ small.pinsPos).trans small.pinStorage
  have pinsBound : (P).header.pins≤g :=
    (Nat.le_mul_of_pos_left _ small.ticksPos).trans small.pinStorage
  have rows : (P).factor.items≤g :=
    (Nat.le_mul_of_pos_right _ (show 0<(P).factor.stride from Nat.succ_pos _)).trans small.resource
  have sp : 0< span := small.spanPos
  have within : (P).lanes≤full := within_of_capacity bits full span sp small.capacity
  have sourceBound : rails*2≤bits := by
    unfold GridSelfHeader.rawSize at raw
    omega
  have rawBound : (P).source.external+(P).literals≤bits := by
    change rails*2+(GridSelfHeader.rawSize w rails compact nparams-rails*2)≤bits
    omega
  have ends : (P).endpoints≤g := sourceBound.trans small.bits
  have rail : (P).endpoints/2≤g := (Nat.div_le_self ..).trans ends
  have len (b : Bank) : b.length P bits full≤g := by
    cases b with
    | raw => exact small.bits
    | selector => exact small.selector
    | resource => exact small.resource
    | ancestors => exact small.full
    | ticks => exact ticks
    | factors | keys | owners => exact rows
    | blocks => exact within.trans small.full
    | rails => exact rail
    | dest => exact ends
    | literals => exact small.pinStorage
  have bank : BankRoom (64*w) P bits full := by
    constructor
    · exact fun b => (Nat.add_le_add_left (len b) _).trans (win.fit b).le
    · intro b c h
      exact (win.disjoint b c h).imp ((Nat.add_le_add_left (len b) _).trans)
        ((Nat.add_le_add_left (len c) _).trans)
  have textB : (P).header.textBase+(P).header.text≤bits := by
    change rails*2+text≤bits
    unfold GridSelfHeader.rawSize at raw
    omega
  have opB : (P).header.operandBase+(P).header.operandBits≤bits := raw
  have start : bits≤(P).header.literalBase := by
    change bits≤10*J
    have := small.bits
    change bits≤g at this
    omega
  have below : (P).header.literalBase+(P).ticks*(P).header.pins≤(P).header.selectorBase := by
    change 10*J+(P).ticks*(P).header.pins≤12*J
    have slots : (P).ticks*(P).header.pins≤g := small.pinStorage
    omega
  refine ⟨bank,win,by omega,by omega,small.ticksPos,small.pinsPos,small.spanPos,
    ticks.trans_lt smallWord,small.factors.trans_lt smallWord,(within.trans small.full).trans_lt smallWord,
    (Nat.le_trans (Nat.le_add_left (P).literals (P).source.external) rawBound).trans_lt
      (small.bits.trans_lt smallWord),ends.trans_lt smallWord,pinsBound.trans_lt smallWord,
    (Nat.add_le_add_left small.pinStorage _).trans_lt (win.fit .literals),
    textB.trans_lt (small.bits.trans_lt smallWord),opB.trans_lt (small.bits.trans_lt smallWord),
    (Nat.add_le_add_left small.selector _).trans_lt (win.fit .selector),?_,rows.trans_lt smallWord,
    small.classes.trans_lt smallWord,small.span.trans_lt smallWord,small.bits.trans_lt smallWord,
    small.full.trans_lt smallWord,within,fun i hi => active_of_lt bits span i sp hi,rawBound⟩
  intro z hz
  rcases hz with ⟨_,ht⟩ | ⟨_,ho⟩ | ⟨hs,_⟩
  · exact Or.inl (ht.trans_le (textB.trans start))
  · exact Or.inl (ho.trans_le (opB.trans start))
  · exact Or.inr (below.trans hs)

theorem canonical_bankRoom (pos : 0<w)
    (small : Small w P bits full (stages*full) K)
    (raw : GridSelfHeader.rawSize w rails compact nparams≤bits) (code : text≤w^2) :
    BankRoom (64*w) P bits full :=
  (canonical_scalars w k n q pins nparams sel text compact rails bits N stages full span pos small raw code).bank

end Hierarchy.GridPinArena

end OAI
