import OAI.Hierarchy.DescentResetPeerCandidates

namespace OAI
/-! # Fixed-address reset peer directory, including its two shared literal tables -/
namespace Hierarchy.DescentResetPeerUnionRAM.Program
open DescentSIMDLookup DescentPackedColony DescentIssuedTerminalId ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

def tablesAt (start oldHosts shapes : ℕ) := start+Candidates.length oldHosts shapes
def scratchAt (start oldHosts shapes oldDegree E b M : ℕ) :=
  tablesAt start oldHosts shapes+Packed.words (Candidates.count shapes oldDegree) E b M
def endAddress (start oldHosts shapes oldDegree E b M : ℕ) :=
  stop (scratchAt start oldHosts shapes oldDegree E b M) (oldHosts*shapes) (Candidates.count shapes oldDegree)

variable {H S D E b M G w : ℕ}
local notation "slots" => Candidates.count S D
local notation "pitch" => H*S
local notation "tableWords" => Packed.words slots E b M
local notation "srcTy" => Fin E → Fin (chunks G M) → Expr
local notation "testTy" => Fin slots → Fin E → Cell b → Bool

def operands (start H S D b M G : ℕ) (old : Bank) (src : Fin E→Fin (chunks G M)→Expr) :=
  Packed.inputs (b:=b) (G:=G) (M:=M) (tablesAt start H S)
    (Candidates.selector old start H S D) src

def program (w start H S D b M G : ℕ) (old : Bank)
    (test : Fin (Candidates.count S D)→Fin E→Cell b→Bool) (src : Fin E→Fin (chunks G M)→Expr) : Procedure w :=
  let first:=DescentStaticWordColumn.program w start (Candidates.literal H S D) (Candidates.length H S)
  let second:=DescentStaticWordColumn.program w (tablesAt start H S) (Packed.literal test M)
    (Packed.words (Candidates.count S D) E b M)
  (first.seq second).seq (machine (operands start H S D b M G old src) w (scratchAt start H S D E b M) (H*S))

def mounted (start H S D M : ℕ) (test : Fin (Candidates.count S D)→Fin E→Cell b→Bool) (m : Memory w) :=
  DescentStaticWordColumn.image (tablesAt start H S) (Packed.literal test M) (Candidates.printed start H S D m)
    (Packed.words (Candidates.count S D) E b M)

def output (start H S D b M G : ℕ) (old : Bank) (test : Fin (Candidates.count S D)→Fin E→Cell b→Bool)
    (src : Fin E→Fin (chunks G M)→Expr) (m : Memory w) :=
  after (operands start H S D b M G old src) (scratchAt start H S D E b M) (H*S) (mounted start H S D M test m)

def clock (start H S D b M G : ℕ) (old : Bank) (src : Fin E→Fin (chunks G M)→Expr) :=
  ((4+10*Candidates.length H S)+(4+10*Packed.words (Candidates.count S D) E b M))+
    ticks (operands start H S D b M G old src) (scratchAt start H S D E b M) (H*S)

structure Space (start H S D E b M G w : ℕ) (old : Bank) (src : Fin E→Fin (chunks G M)→Expr) : Prop where
  oldFits : old.Fits w start
  oldSize : H*D ≤ old.size
  rows : ∀e c,(src e c).Fits w start
  endFits : endAddress start H S D E b M < 2^w

private theorem atEnd {start : ℕ} {old : Bank} {src : srcTy} (safe : Space start H S D E b M G w old src) :
    scratchAt start H S D E b M < 2^w :=
  ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans_lt safe.endFits

private theorem candidateSpace {start : ℕ} {old : Bank} {src : srcTy} (safe : Space start H S D E b M G w old src) :
    Candidates.Setup old start H S D w :=
  ⟨safe.oldFits,safe.oldSize,(Nat.le_add_right ..).trans_lt (atEnd safe)⟩

private theorem bankSpace (bank : Bank) {base : ℕ} (inside : bank.base+bank.size ≤ base)
    (wide : base < 2^w) : bank.Fits w base :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (inside.trans_lt wide),inside⟩

theorem selectorFits {start : ℕ} {old : Bank} (safe : Candidates.Setup old start H S D w) (j : Fin slots) :
    (Candidates.selector old start H S D j).Fits w (tablesAt start H S) := by
  have early:=safe.endRoom
  have cf := bankSpace (Candidates.current start H S)
    (by change start+stride pitch ≤ start+(2*stride pitch+stride H);omega) early
  have sf := bankSpace (Candidates.starts start H S)
    (by change start+stride pitch+stride pitch ≤ start+(2*stride pitch+stride H);omega) early
  have of_ := bankSpace (Candidates.offsets start H S)
    (by change start+2*stride pitch+stride H ≤ start+(2*stride pitch+stride H);omega) early
  have oldFit : old.Fits w (tablesAt start H S) :=
    ⟨safe.oldFit.1,safe.oldFit.2.1,safe.oldFit.2.2.trans (Nat.le_add_right ..)⟩
  unfold Candidates.selector
  split
  · dsimp only
    split
    · exact ⟨⟨oldFit,⟨⟨sf,trivial⟩,trivial⟩⟩,trivial,⟨⟨of_,⟨oldFit,⟨⟨sf,trivial⟩,trivial⟩⟩⟩,trivial⟩,trivial⟩
    · exact ⟨⟨cf,trivial⟩,trivial,⟨⟨of_,⟨cf,trivial⟩⟩,trivial⟩,trivial⟩
  · trivial

theorem room {start : ℕ} {old : Bank} {src : srcTy} (safe : Space start H S D E b M G w old src) :
    Room (operands start H S D b M G old src) (scratchAt start H S D E b M) pitch w := by
  let end_:=scratchAt start H S D E b M
  have wide:=atEnd safe
  have tab : tablesAt start H S ≤ end_ := Nat.le_add_right ..
  have low : start ≤ end_ := (Nat.le_add_right ..).trans tab
  have many : 3 ≤ slots := Nat.le_add_left ..
  have nr : pitch ≤ stride pitch := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have large := safe.endFits
  change end_+slots*stride pitch+3*pitch < 2^w at large
  have per : slots ≤ slots*stride pitch := by
    simpa only [stride, Nat.mul_one] using Nat.mul_le_mul_left slots (Nat.two_pow_pos (pageBits pitch))
  refine ⟨fun j=>ProtocolRAMGeneratedWrite.fits_mono _ tab (selectorFits (candidateSpace safe) j),?_,many,by omega,by omega,safe.endFits⟩
  intro j q
  let x:=finProdFinEquiv.symm q
  have fin:=Nat.mul_le_mul_right (2^(b*M)) (Packed.slot j x.1).isLt
  rw [Nat.succ_mul] at fin
  exact ⟨bankSpace _ (by
    change tablesAt start H S+(Packed.slot j x.1).val*2^(b*M)+2^(b*M) ≤ tablesAt start H S+slots*E*2^(b*M)
    omega) wide,ProtocolRAMGeneratedWrite.fits_mono _ low (safe.rows x.1 x.2)⟩

theorem any {start : ℕ} (old : Bank) (test : testTy) (src : srcTy)
    (safe : Space start H S D E b M G w old src) (m : Memory w) :
    (program w start H S D b M G old test src).Exec m (output start H S D b M G old test src m)
        (clock start H S D b M G old src) ∧
    CheapCode (program w start H S D b M G old test src) ∧
    ∀a,a < start ∨ endAddress start H S D E b M ≤ a → output start H S D b M G old test src m a=m a := by
  have one:=Candidates.install old (candidateSpace safe) m
  have two:=Packed.install (tablesAt start H S) test M (Candidates.printed start H S D m) (atEnd safe)
  have three:=DescentResetPeerUnionRAM.any _ (room safe) (mounted start H S D M test m)
  refine ⟨Procedure.Exec.then (Procedure.Exec.then one.1 two.1) three.1,
    cheap_seq (cheap_seq (DescentStaticWordColumn.cheap w start (Candidates.literal H S D)
      (Candidates.length H S)) two.2.1) three.2.1,?_⟩
  have le₁ : start ≤ tablesAt start H S := Nat.le_add_right ..
  have le₂ : tablesAt start H S ≤ scratchAt start H S D E b M := Nat.le_add_right ..
  have le₃ : scratchAt start H S D E b M ≤ endAddress start H S D E b M :=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  intro a h
  rcases h with lo|hi
  · exact (three.2.2 a (.inl (lo.trans_le (le₁.trans le₂)))).trans
      ((two.2.2.2 a (.inl (lo.trans_le le₁))).trans (one.2 a (.inl lo)))
  · exact (three.2.2 a (.inr hi)).trans
      ((two.2.2.2 a (.inr (le₃.trans hi))).trans (one.2 a (.inr ((le₂.trans le₃).trans hi))))

/-- The two consecutive literal installations preserve the previously measured
old roster and all short packed predecessor records. -/
theorem loaded {start : ℕ} (old : Bank) (test : testTy) (src : srcTy)
    (safe : Space start H S D E b M G w old src) (m : Memory w)
    (peers : Fin H→Fin D→Option (Fin H))
    (reads : ∀h d,m (old.base+(h.val*D+d.val))=(target (peers h d):Word w))
    (values : Fin E→Fin pitch→Fin G→Cell b)
    (rows : ∀e h c,(src e c).eval m (h.val:Word w)=((data (M:=M) (values e) (h,c)).val:Word w))
    (pos : 0 < M) (blank : ∀d e,test d e 0=false) :
    let q:=operands start H S D b M G old src
    let n:=mounted start H S D M test m
    (∀v j,(q.other j).eval n (v.val:Word w)=(target (Candidates.candidate peers v j):Word w)) ∧
    (∀(v : Fin pitch) (j : Fin slots),(∃l,(q.evidence j l).eval n (v.val:Word w) ≠ 0) ↔
       ∃e g,test j e (values e v g)=true) := by
  intro q n
  have first:=Candidates.install old (candidateSpace safe) m
  have second:=Packed.install (tablesAt start H S) test M (Candidates.printed start H S D m) (atEnd safe)
  have midFrame a (ha:a < tablesAt start H S) : n a=Candidates.printed start H S D m a:=second.2.2.2 _ (.inl ha)
  refine ⟨fun v j=>(eval_below _ _ _ n (selectorFits (candidateSpace safe) j) midFrame).trans
    (Candidates.selected old (candidateSpace safe) m peers reads v j),?_⟩
  intro v j
  by_cases empty : E=0
  · subst E
    exact ⟨fun ⟨l,_⟩=>Fin.elim0 (Fin.cast (Nat.zero_mul (chunks G M)) l),
      fun ⟨e,_⟩=>Fin.elim0 e⟩
  have many:= (room safe).candidates
  have large:=(room safe).localWord
  have power : 2^(b*M) ≤ tableWords := by
    have ex : 0 < slots*E := Nat.mul_pos (by omega) (by omega)
    simpa only [Packed.words, Nat.one_mul] using Nat.mul_le_mul_right (2^(b*M)) ex
  exact Packed.hit (tablesAt start H S) test _ src values n pos blank
    (power.trans_lt ((Nat.le_add_left ..).trans_lt (atEnd safe))) (by omega) second.2.2.1
    (fun e h c=>(eval_below _ _ m n (safe.rows e c) (fun a ha=>
      (midFrame a (ha.trans_le (Nat.le_add_right ..))).trans (first.2 _ (.inl ha)))).trans (rows e h c)) v j

end
end Hierarchy.DescentResetPeerUnionRAM.Program

end OAI
