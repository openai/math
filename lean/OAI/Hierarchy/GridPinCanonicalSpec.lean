import OAI.Hierarchy.GridPinArenaRoom
import OAI.Hierarchy.GridPinStateFrames
import OAI.Hierarchy.GridPinScheduledOffsets
import OAI.Hierarchy.GridPinFinalScatters
import OAI.Hierarchy.GridPinCapturedSources

namespace OAI
/-! # Native evaluator input publisher with canonical exterior numbering -/

namespace Hierarchy.GridPinPublisher
open ThreeFlat
open RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open GridThrough FactorPinIntervals GridPinPrefixMemory GridPinNativeLoops FactorBucketRAM
open scoped Fin.CommRing Classical
noncomputable section

variable {scale k n q d nparams ell text compact rails S N stages full span : ℕ}

abbrev actualPlan (scale k n q d nparams ell text compact rails S N stages full span : ℕ) : Plan :=
  canonical scale k n q d nparams ell text compact rails S N stages full span

/-- The outer evaluator's physical rank table is the identity on the original
exterior rows, as supplied by its preceding native seed pass. -/
def exteriorRails (room : rails*2≤S) : Fin rails↪Fin (S/2) where
  toFun e := ⟨e.val,by have := e.isLt;omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun t : Fin (S/2)=>t.val) h)

/-- Incoming RAM words from the geometric dispatcher and the terminal
ancestor row. Captured values are the actual memories resulting from the
original input and the private selector-guess program. -/
structure Raw (P : Plan) (Q : Layout (Cell k n×Fin q) S N d)
    (ht : 0<(n+1)^k*q) (cost : Fin N→Fin (k+2)→ℕ) (lane : Fin full→Fin N)
    (capture incoming : Memory (64*scale)) : Prop where
  key : ∀ f, incoming (P.factor.keys+f.val)=(factorKey scale cost f:Word (64*scale))
  owner : ∀ f, incoming (P.factor.owners+f.val)=((FactorAllocation.owner ht scale cost f).val:Word (64*scale))
  inputLength : ∀ f : Fin N,incoming (P.factor.resource+f.val*P.factor.stride+P.factor.amount)=
    ((intervalBits Q.origin f).length:Word (64*scale))
  ancestor : ∀ b : Fin full,incoming (P.bucket.owners+b.val)=((lane b).val:Word (64*scale))
  original : ∀ j<S, incoming (P.source.originals+j)=capture (P.source.originals+j)
  selector : ∀ i<P.header.selector,incoming (P.header.selectorBase+i)=capture (P.header.selectorBase+i)

variable {W : ℕ} (P : Plan)

/-- Write the ordinal lookup table before entering the six-phase publisher. -/
def withRails (m : Memory W) (r : ℕ) := FactorBucketRAM.iterRows seedStep
  (seedWords W r P.source.rails 1 0) m r

theorem canonicalProgram_exec {W : ℕ} (m : Memory W) (r : ℕ) (budget : ℕ)
    (rfit : r<2^W) (main : (P.program W).Exec (withRails P m r) (P.output (withRails P m r)) budget) :
    (P.canonicalProgram W r).Exec m (P.output (withRails P m r))
      (3+r*(1+seedOps.length)+budget) := by
  have seed : (procedure seedOps (seedWords W r P.source.rails 1 0)).Exec m (withRails P m r)
      (3+r*(1+seedOps.length)) := Procedure.Spec.exec
        (loop_spec seedOps seedStep (fun _ _ _ _ _ _=>seed_trace ..)
          (seedWords W r P.source.rails 1 0) r rfit rfl) m trivial
  intro pcs regs slots mach pc reg pub exit install data cfg mem first eqn
  exact Procedure.Exec.then seed main mach pc reg pub exit install data cfg mem first eqn

section Real
variable {F : Type} [Field F] [Fintype F] {u tp tr tk ep er ek : ℕ}
variable (X : Catalyst.Approximation F k u) (enc : FieldCode F (64*scale))
variable (params : Fin nparams→Word (64*scale)) (recv : Machine (64*scale) tp tr tk)
    (eval : Machine (64*scale) ep er ek) (x : Fin (rails*2)→Bool) (sel : Fin ell→Bool)

def capture : Memory (64*scale) :=
  GridSelfHeader.captured (B:=compact) X enc params recv eval x (12*GridDescription.sector scale) sel

set_option maxHeartbeats 2000000 in
theorem canonicalSpec (Q : Layout (Cell k n×Fin q) S N d) (ht : 0<(n+1)^k*q)
    (cost : Fin N→Fin (k+2)→ℕ) (lane : Fin full→Fin N)
    (bucket : Fin S→Fin full) (quotient : ∀ j,(bucket j).val=j.val/span)
    (trueOwner : ∀ j,lane (bucket j)=Q.origin j)
    (dispatch : ∀ f,GridTicks.index (Q.owner f)=FactorAllocation.owner ht scale cost f)
    (order : ∀ t,Q.rows t=FactorAllocation.factors scale cost (List.finRange N) (GridTicks.index t))
    (direction : Fin rails→Fin k) (room : rails*2≤S)
    (paired : ∀ e,Q.origin (pairPorts (exteriorRails room) (e,true))=
      Q.origin (pairPorts (exteriorRails room) (e,false)))
    (fit : text≤ scale^2) (pos : 0< scale)
    (hw : ∀t,Q.header t=GridReceiverHeader.header text fit
      (GridDescription.code (q:=scale^2) recv eval) ((GridTicks.index t).val:Word (64*scale)) params sel)
    (fixed : Q.advice=GridPinCapturedSources.advice (e:=rails) (compact:=compact) X enc params recv eval)
    (size : GridSelfHeader.rawSize scale rails compact nparams≤S)
    (sep : GridSelfHeader.rawSize scale rails compact nparams≤12*GridDescription.sector scale)
    (canon : P=canonical scale k n q d nparams ell text compact rails S N stages full span)
    (small : GridPinArena.Small scale P S full (stages*full) ((20*(scale+1)+2)^(k+2)))
    (incoming : Memory (64*scale))
    (raw : Raw P Q ht cost lane (capture (compact:=compact) X enc params recv eval x sel) incoming) :
    let A := PinAssignment.ofFactorIntervals Q direction (pairPorts (exteriorRails room)) paired
    (P.canonicalProgram (64*scale) rails).Spec (·=incoming)
      (fun _ out=>Published A P out ∧ ∀a,Outside P rails a→ out a=incoming a)
      (3+rails*(1+seedOps.length)+P.budget (64*scale)) := by
  subst P
  let P := canonical scale k n q d nparams ell text compact rails S N stages full span
  intro A
  let K := (20*(scale+1)+2)^(k+2)
  let boot := withRails P incoming rails
  let R := GridPinArena.canonical_scalars scale k n q d nparams ell text compact rails S N stages full span pos small size fit
  have railCount : Bank.rails.length P S full=rails := by simp [Bank.length,P,canonical]
  have start (b : Bank) (hb : b≠.rails) (i : ℕ) (hi : i<b.length P S full) :
      boot (b.base P+i)=incoming (b.base P+i) :=
    seed_frame P.source.rails 1 0 rails incoming (railCount ▸ R.bank.fit .rails) _
      (railCount ▸ R.bank.away b .rails hb hi)
  have stepPos : 0<P.factors → 0<P.factor.items := fun h=>Nat.pos_of_mul_pos_left h
  let geo : PrefixGeometry (64*scale) P full :=
    ⟨R.factorsFit.le,R.itemsFit,stepPos,R.within,rfl⟩
  have originWords (f : Fin N) : boot (P.factor.owners+f.val)=((FactorAllocation.owner ht scale cost f).val:Word (64*scale)) :=
    (start .owners (by decide) _ f.isLt).trans (raw.owner f)
  have laneWords (b : Fin full) : boot (P.bucket.owners+b.val)=((lane b).val:Word (64*scale)) :=
    (start .ancestors (by decide) _ b.isLt).trans (raw.ancestor b)
  have own : PrefixOwners P boot := by
    constructor
    · intro f
      let v : Fin N := ⟨f.val,f.isLt⟩
      let t := FactorAllocation.owner ht scale cost v
      have bound : t.val < P.ticks := t.isLt
      have read : boot (P.factor.owners+f.val)=(t.val : Word (64*scale)) := originWords v
      exact ((congrArg Fin.val read).trans (Fin.val_cast_of_lt (bound.trans R.ticksFit))).trans_lt bound
    · intro b
      let s : Fin full := ⟨b.val,b.isLt.trans_le R.within⟩
      have bound : (lane s).val < P.factor.items := (lane s).isLt
      exact ((congrArg Fin.val (laneWords s)).trans (Fin.val_cast_of_lt (bound.trans R.itemsFit))).trans_lt bound
  have immutable (b : Bank) (bt : b≠.ticks) (bf : b≠.factors) (bb : b≠.blocks)
      (i : ℕ) (hi : i<b.length P S full) :
      P.bucketed boot (b.base P+i)=boot (b.base P+i) := R.bank.bucketed_read geo boot own b bt bf bb _ hi
  have keep (b : Bank) (bl : b≠.literals) (i : ℕ) (hi : i<b.length P S full) :
      P.initialized boot (b.base P+i)=P.bucketed boot (b.base P+i) := by
    have h := R.bank.away b .literals bl hi
    change b.base P+i<P.header.literalBase ∨ P.header.literalBase+P.ticks*P.header.pins≤b.base P+i at h
    simp [Plan.initialized,fillSegment,show ¬(P.header.literalBase≤b.base P+i ∧
      b.base P+i<P.header.literalBase+P.ticks*P.header.pins) by omega]
  have lens (t) : (Q.header t).length=P.headerSize := by rw [hw,GridReceiverHeader.length];rfl
  have lenAddr (f : Fin N) : f.val*(k+2)+1<N*(k+2) := by
    have le:=Nat.mul_le_mul_right (k+2) f.isLt
    rw [Nat.succ_mul] at le
    omega
  have Nslab : N≤GridPinArena.slab scale :=
    (Nat.le_mul_of_pos_right N (by omega : 0<k+2)).trans small.resource
  have blk (j : Fin S) : P.bucketed boot (P.source.blocks+j.val/span)+((j.val%span:ℕ):Word (64*scale))=
      ((GridPinAddressImage.code (Q.address j)).val:Word (64*scale)) := by
    apply scheduled_offsets P Q ht scale cost boot lane dispatch order lens rfl rfl rfl rfl rfl rfl rfl rfl rfl
      R.within R.active bucket quotient (fun j=>by rw [quotient];exact bucket_visited R.spanPos j) trueOwner
      R.spanPos R.factorsFit R.itemsFit R.ticksFit.le R.classesFit.le R.lanesFit R.spanFit R.bitsFit R.bank
      (by change 1<k+2;omega)
    · intro f;exact (R.bank.seeded_read boot .keys (by decide) _ f.isLt).trans
        ((start .keys (by decide) _ f.isLt).trans (raw.key f))
    · intro f;exact (R.bank.seeded_read boot .owners (by decide) _ f.isLt).trans (originWords f)
    · intro f
      have read := (R.bank.seeded_read boot .resource (by decide) _ (lenAddr f)).trans
        (start .resource (by decide) _ (lenAddr f))
      change P.seeded boot (P.factor.resource+(f.val*(k+2)+1))=incoming (P.factor.resource+(f.val*(k+2)+1)) at read
      have actual : incoming (P.factor.resource+f.val*(k+2)+1)=((intervalBits Q.origin f).length:Word (64*scale)) :=
        raw.inputLength f
      change P.seeded boot (P.factor.resource+f.val*(k+2)+1)=_
      rw [Nat.add_assoc] at actual ⊢
      exact read.trans actual
    · intro b;exact (R.bank.factorized_read geo boot own.factor .ancestors (by decide) (by decide) _ b.isLt).trans (laneWords b)
    · intro b;exact (Nat.add_lt_add_left (b.isLt.trans_le small.full) _).trans (R.window.fit .blocks)
    · intro b c;exact R.window.ne .ancestors .blocks (by decide) (b.isLt.trans_le small.full) (c.isLt.trans_le small.full)
    · intro f b;exact R.window.ne .factors .blocks (by decide) (f.isLt.trans_le Nslab) (b.isLt.trans_le small.full)
  have receive (b : Bank) (b0 : b≠.rails) (b1 : b≠.ticks) (b2 : b≠.factors) (b3 : b≠.blocks)
      (i : ℕ) (hi : i<b.length P S full) :
      P.bucketed boot (b.base P+i)=incoming (b.base P+i) :=
    (immutable b b1 b2 b3 i hi).trans (start b b0 i hi)
  have headerFrame (a : ℕ) (ha : GridPinHeaderNative.source P.header a) :
      P.bucketed boot a=capture (compact:=compact) X enc params recv eval x sel a := by
    change (rails*2≤a ∧ a<rails*2+text) ∨
      (rails*2+scale^2+compact*scale^2≤a ∧ a<rails*2+scale^2+compact*scale^2+(nparams+GridReceiverHeader.count scale)*(64*scale)) ∨
      (12*GridDescription.sector scale≤a ∧ a<12*GridDescription.sector scale+ell) at ha
    rcases ha with h | h | h
    · have hi : a<S := by unfold GridSelfHeader.rawSize at size;omega
      have eqn := (receive .raw (by decide) (by decide) (by decide) (by decide) a hi).trans (raw.original a hi)
      change P.bucketed boot (0+a)=capture (compact:=compact) X enc params recv eval x sel (0+a) at eqn
      simpa only [Nat.zero_add] using eqn
    · have hi : a<S := by unfold GridSelfHeader.rawSize at size;omega
      have eqn := (receive .raw (by decide) (by decide) (by decide) (by decide) a hi).trans (raw.original a hi)
      change P.bucketed boot (0+a)=capture (compact:=compact) X enc params recv eval x sel (0+a) at eqn
      simpa only [Nat.zero_add] using eqn
    · let u:=a-12*GridDescription.sector scale
      have idx : u<ell := by dsimp [u];omega
      have eqn : 12*GridDescription.sector scale+u=a := by dsimp [u];omega
      exact eqn ▸ (receive .selector (by decide) (by decide) (by decide) (by decide) u idx).trans (raw.selector u idx)
  have ext : P.source.external=rails*2 := rfl
  have rawEnd : P.source.external+P.literals=GridSelfHeader.rawSize scale rails compact nparams := by
    change rails*2+(GridSelfHeader.rawSize scale rails compact nparams-rails*2)=_
    unfold GridSelfHeader.rawSize;omega
  have tickFit (t : Cell k n×Fin q) : (GridTicks.index t).val<2^(64*scale) := (GridTicks.index t).isLt.trans R.ticksFit
  have headerAt (t : Cell k n×Fin q) (i : Fin d) : P.initialized boot (P.source.literal+(GridPinAddressImage.code (t,i)).val)=
      ((GridPinLiteralImage.headerOnly Q t i).toNat:Word (64*scale)) := by
    have hit := (GridPinAddressImage.code (t,i)).isLt
    change (GridPinAddressImage.code (t,i)).val < (n+1)^k*(q*d) at hit
    have inBlock : (GridPinAddressImage.code (t,i)).val<P.ticks*P.header.pins := by
      change _<((n+1)^k*q)*d;simpa only [Nat.mul_assoc] using hit
    have h := GridPinCapturedSources.framed_header (compact:=compact) (start:=12*GridDescription.sector scale)
      (literal:=P.source.literal) (pins:=d) X enc params recv eval x sel sep fit pos (GridTicks.index t).val i.val
      (tickFit t) i.isLt (P.bucketed boot) headerFrame
    have formula : P.source.literal+(GridPinAddressImage.code (t,i)).val =
        P.header.literalBase+(i.val+P.header.pins*(GridTicks.index t).val) := by
      rw [GridPinAddressImage.code_val]
      change P.source.literal+((GridTicks.index t).val*d+i.val)=
        P.source.literal+(i.val+d*(GridTicks.index t).val)
      ring
    have live : P.header.literalBase ≤ P.source.literal+(GridPinAddressImage.code (t,i)).val ∧
        P.source.literal+(GridPinAddressImage.code (t,i)).val < P.header.literalBase+P.ticks*P.header.pins := by
      change P.source.literal ≤ P.source.literal+_ ∧ P.source.literal+_ < P.source.literal+_
      exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left inBlock _⟩
    change (if _ then _ else _) = _
    rw [ite_eq_left live,formula]
    have word : GridPinHeaderNative.initialWord (64*scale) P.header (fun a => (P.bucketed boot a).val)
        (P.header.literalBase+(i.val+P.header.pins*(GridTicks.index t).val)) =
        (((GridReceiverHeader.header text fit (GridDescription.code (q:=scale^2) recv eval)
          ((GridTicks.index t).val : Word (64*scale)) params sel)[i.val]?).getD false).toNat := h
    rw [word,GridPinLiteralImage.headerOnly,hw]
    split <;> rename_i valid
    · simp only [List.getElem?_eq_getElem valid,Option.getD_some]
    · simp only [List.getElem?_eq_none (Nat.le_of_not_gt valid),Option.getD_none]
  have endSep : P.source.dest+rails*2≤P.source.literal := by
    have two := R.bank.disjoint .dest .literals (by decide)
    have J := Nat.two_pow_pos (32*scale)
    change 9*GridDescription.sector scale+rails*2≤10*GridDescription.sector scale ∨ _ at two
    rcases two with h | h
    · exact h
    · change 10*GridDescription.sector scale+_≤9*GridDescription.sector scale at h
      change 0<GridDescription.sector scale at J;omega
  have railBound {i : ℕ} (h : i<rails) : i<Bank.rails.length P S full:=by rw [railCount];exact h
  have railFit : P.source.rails+rails≤2^(64*scale):=by
    have result:=R.bank.fit .rails
    change P.source.rails+Bank.rails.length P S full≤_ at result
    rwa [railCount] at result
  have literalFit : P.source.literal+(n+1)^k*(q*d)≤2^(64*scale):=by
    have result:=R.bank.fit .literals
    change P.source.literal+((n+1)^k*q)*d≤_ at result
    simpa only [Nat.mul_assoc] using result
  have endReal : Published A P (P.output boot) ∧ ∀a,
      (a<P.source.dest ∨ P.source.dest+rails*2≤a) →
      (a<P.source.literal ∨ P.source.literal+(n+1)^k*(q*d)≤a) →
      P.output boot a=P.initialized boot a := published_banks P Q (exteriorRails room) direction paired boot rfl R.bitFit
    R.bitsFit.le R.two R.spanFit R.literalsFit R.endsFit headerAt
    (by
      intro i hi;let j : Fin S:=⟨P.source.external+i,by have h:=R.bitFit;omega⟩
      have restored:=(keep .raw (by decide) j.val j.isLt).trans
        ((receive .raw (by decide) (by decide) (by decide) (by decide) j.val j.isLt).trans (raw.original j.val j.isLt))
      apply restored.trans
      have h0 : P.source.originals=0:=rfl
      rw [h0,Nat.zero_add,fixed]
      apply GridPinCapturedSources.captured_advice X enc params recv eval x sel sep j
      · change rails*2≤rails*2+i;omega
      · rw [←rawEnd];change P.source.external+i<P.source.external+P.literals;omega)
    (by intro j hj;rw [fixed];apply GridPinCapturedSources.unscattered
        rcases hj with low|high
        · exact Or.inl (by simpa only [ext] using low)
        · exact Or.inr (by simpa only [rawEnd] using high))
    (by
      intro i hi;have h : i/2<rails := by omega
      have restored:=(keep .rails (by decide) _ (railBound h)).trans
        (immutable .rails (by decide) (by decide) (by decide) _ (railBound h))
      apply restored.trans
      have value:=seed_readback P.source.rails 1 0 rails incoming railFit (i/2) h
      have rank : railOfNat (exteriorRails room) (i/2)=i/2 := by rw [railOfNat,dite_eq_left h];rfl
      rw [rank]
      change iterRows seedStep (seedWords (64*scale) rails P.source.rails 1 0) incoming rails (P.source.rails+i/2)=_
      simpa only [Nat.mul_one,Nat.add_zero] using value)
    (by
      intro j
      have bound:=bucket_visited R.spanPos j
      have restored:=keep .blocks (by decide) (j.val/span) bound
      exact (congrArg (fun t : Word (64*scale)=>t+((j.val%span:ℕ):Word (64*scale))) restored).trans (blk j))
    (by intro j;exact R.bank.address .blocks (bucket_visited R.spanPos j))
    (R.bank.fit .raw) literalFit railFit (R.bank.fit .dest) endSep
    (by
      intro i hi
      have pin : i<Bank.literals.length P S full := by change i<((n+1)^k*q)*d;simpa [Nat.mul_assoc] using hi
      exact ⟨fun j=>R.bank.ne .literals .blocks (by decide) pin (bucket_visited R.spanPos j),
        fun j=>R.bank.ne .literals .raw (by decide) pin j.isLt,
        fun e=>R.bank.ne .literals .rails (by decide) pin (railBound e.isLt)⟩)
    (by intro i hi;exact ⟨fun j=>R.bank.ne .dest .blocks (by decide) hi (bucket_visited R.spanPos j),
      fun e=>R.bank.ne .dest .rails (by decide) hi (railBound e.isLt)⟩)
  have run : (P.canonicalProgram (64*scale) rails).Exec incoming (P.output boot)
      (3+rails*(1+seedOps.length)+P.budget (64*scale)) := canonicalProgram_exec P incoming rails _ (by have h:=R.endsFit;change rails*2<_ at h;omega)
    (Plan.execute P boot R.ticksFit R.factorsFit R.lanesFit R.literalsFit R.endsFit R.wordPos R.pinsPos
      R.pinsFit R.outFit R.textFit R.opsFit R.selFit R.separate)
  intro pcs regs slots machine pc reg pub exit install data cfg mem entry initial
  obtain ⟨ticks,within,last,out,advance,done,output⟩:=run machine pc reg pub exit install data cfg mem entry initial
  subst out
  refine ⟨ticks,within,last,_,advance,done,endReal.1,?_⟩
  intro a ha
  obtain ⟨ar,at',af,ab,al,ad⟩ := ha
  have literals : a<P.source.literal ∨ P.source.literal+(n+1)^k*(q*d)≤a := by
    change a<P.source.literal ∨ P.source.literal+((n+1)^k*q)*d≤a at al
    simpa only [Nat.mul_assoc] using al
  rw [endReal.2 a ad literals]
  have away : a<P.header.literalBase ∨ P.header.literalBase+P.ticks*P.header.pins≤a := al
  change (if _ then _ else _)=_
  rw [ite_eq_right (by omega),R.bank.bucketed_outside geo boot own a at' af ab]
  exact seed_frame P.source.rails 1 0 rails incoming railFit a ar

end Real

end
end Hierarchy.GridPinPublisher

end OAI
