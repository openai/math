import OAI.Hierarchy.DescentParentBoundedKey
import OAI.Hierarchy.DescentResetParentAddresses
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Unconditional execution of the bounded parent-directory publisher -/
namespace Hierarchy.DescentResetParentDate
open DescentCensusRAM DescentDyadicSpan ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
abbrev endAddress := DescentResetParentAperture.endAddress
open DescentResetParentAperture (codes ids banks first bins parent)
variable (base slots pad shapes : ℕ) (flags : Bank)

def sumWords {w : ℕ} (base : ℕ) (m : Memory w) : ℕ→ℕ
  | 0=>0
  | i+1=>sumWords base m i+(m (base+i)).val
def head {w : ℕ} (m : Memory w) :=DescentStaticWordColumn.image base (fun j=>j/shapes) m slots
def «prefix» {w : ℕ} (m : Memory w) :=ProtocolRAMEndpointPrefix.image (ids base slots).base
  (sumWords flags.base (head base slots shapes m)) (head base slots shapes m) slots

def key :=DescentParentBoundedKey.destination (bins base slots pad) pad flags (ids base slots)
def value :=Expr.lookup (codes base slots) .row
variable {w : ℕ}
local notation "k₀" => key base slots pad flags
local notation "v₀" => value base slots

def program (w : ℕ) (room : endAddress base slots pad<2^w) :=
  (DescentStaticWordColumn.program w base (fun j=>j/shapes) slots).seq
    ((ProtocolRAMEndpointPrefix.exclusive w flags.base (ids base slots).base slots).seq
     (tally (banks base slots pad w room) k₀ v₀))

def ticks (w : ℕ) (room : endAddress base slots pad<2^w) :=
  (4+10*slots)+((10+(3+12*slots))+tallyCost (banks base slots pad w room) k₀ v₀)

def memory (m : Memory w) (room : endAddress base slots pad<2^w) :=
  let p:=«prefix» base slots shapes flags m
  let target:=DescentParentBoundedKey.targetIn (n:=slots) pad flags (ids base slots) p
  let wt:=fun i:Fin slots=>((v₀).eval p (i.val:Word w)).val
  afterAdd (banks base slots pad w room) k₀ v₀ target wt (ProtocolRAM.image (bins base slots pad) (pad+1) (.lit 0) p)

private theorem scatter_high {n B : ℕ} (S : Banks w n B) (k v : Expr) (tag : Fin n→Fin B) (wt : Fin n→ℕ)
    (m : Memory w) (a : ℕ) (high : S.bins+B≤a) : afterAdd S k v tag wt m a=m a := by
  let dest:=fun i:Fin n=>S.bins+(tag i).val
  have tail (d : ℕ) (hd : d<2) (e : Expr) (f : Fin n→ℕ) (o : Memory w) : issued S d e f o a=o a := by
    apply issued_away S d e f o a (.inr (by have:=S.beforeBins;omega))
    intro j
    have:=j.isLt
    have:=S.beforeBins
    dsimp only [atSlot]
    omega
  change ProtocolRAMWeightedScatter.image dest wt _ n a=m a
  rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ (fun i=>by have:=(tag i).isLt;dsimp [dest];omega)]
  exact (tail 1 (by decide) _ _ _).trans (tail 0 (by decide) _ _ _)

theorem prefix_run (m : Memory w) (early : flags.Fits w base) (rows : slots≤flags.size)
    (room : endAddress base slots pad<2^w) :
    let p:=«prefix» base slots shapes flags m
    ((DescentStaticWordColumn.program w base (fun j=>j/shapes) slots).seq
      (ProtocolRAMEndpointPrefix.exclusive w flags.base (ids base slots).base slots)).Exec m p
      ((4+10*slots)+(10+(3+12*slots))) ∧
    (∀i,i<base ∨ first base slots≤ i → p i=m i) := by
  intro p
  have cut:=(DescentResetParentAperture.fits room).2.2.1
  have length:=span_ge slots
  have count:=span_ge (slots+1)
  have firstLow:base+slots≤(ids base slots).base:=Nat.add_le_add_left length _
  have high:(ids base slots).base+(slots+1)≤first base slots:=Nat.add_le_add_left count _
  have earlier:flags.base+slots≤base:=(Nat.add_le_add_left rows _).trans early.2.2
  have one : (DescentStaticWordColumn.program w base (fun j=>j/shapes) slots).Exec m
      (head base slots shapes m) (4+10*slots):=DescentStaticWordColumn.mount base slots (fun j=>j/shapes) m (by omega)
  have two : (ProtocolRAMEndpointPrefix.exclusive w flags.base (ids base slots).base slots).Exec
      (head base slots shapes m) p (10+(3+12*slots)):=ProtocolRAMEndpointPrefix.run flags.base (ids base slots).base slots
    (sumWords flags.base (head base slots shapes m)) (head base slots shapes m) (by omega) cut rfl
    (fun i _=>by simp [sumWords])
  refine ⟨by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then one two machine pc regs pubs exit rom advice cfg memory enter same,?_⟩
  rintro i (lo|hi)
  · exact (ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl (by omega))).trans
      (DescentStaticWordColumn.frame _ _ _ _ i (.inl lo))
  · exact (ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inr (by omega))).trans
      (DescentStaticWordColumn.frame _ _ _ _ i (.inr (by omega)))

theorem any (m : Memory w) (early : flags.Fits w base) (rows : slots≤flags.size)
    (room : endAddress base slots pad<2^w) :
    (program base slots pad shapes flags w room).Exec m (memory base slots pad shapes flags m room)
      (ticks base slots pad flags w room) ∧ CheapCode (program base slots pad shapes flags w room) ∧
    (∀i,i<base ∨ endAddress base slots pad≤ i → memory base slots pad shapes flags m room i=m i) ∧
    ∀j : Fin (pad+1),memory base slots pad shapes flags m room (bins base slots pad+j.val)=
      (sumAt (DescentParentBoundedKey.targetIn (n:=slots) pad flags (ids base slots) («prefix» base slots shapes flags m))
        (fun i:Fin slots=>((v₀).eval («prefix» base slots shapes flags m) (i.val:Word w)).val) j:Word w) := by
  let S:=banks base slots pad w room
  let p:=«prefix» base slots shapes flags m
  let o:=ProtocolRAM.image S.bins (pad+1) (.lit 0) p
  let tags:=DescentParentBoundedKey.targetIn (n:=slots) pad flags (ids base slots) p
  let wt:=fun i:Fin slots=>((v₀).eval p (i.val:Word w)).val
  obtain ⟨cf,idf,cut,_⟩:=DescentResetParentAperture.fits room
  have low : base≤S.first:=by
    change base≤base+span slots+span (slots+1)
    omega
  have flagFit : flags.Fits w S.first:=⟨early.1,early.2.1,early.2.2.trans low⟩
  have keyFit:=DescentParentBoundedKey.fits S flagFit idf
  have valFit : (v₀).Fits w S.first:=⟨cf,trivial⟩
  have bs:S.first≤S.bins:=by have:=S.scratch;have:=S.beforeTape;have:=S.beforeBins;omega
  have clear (i : ℕ) (hi : i<S.first) : o i=p i:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (hi.trans_le bs))
  have small : pad<2^w:=by have:=S.finish;omega
  have write : (add S k₀ v₀).Exec o (afterAdd S k₀ v₀ tags wt o) (addCost S k₀ v₀) := add_exec S k₀ v₀ tags wt o keyFit valFit
    (fun i=>(eval_below _ _ p o keyFit clear).trans (DescentParentBoundedKey.digit S.bins pad flags (ids base slots) p i small))
    (fun i=>by change _=(((v₀).eval p _).val:Word w); simpa using eval_below v₀ (i.val:Word w) p o valFit clear)
  have wipe : (scan w S.bins (pad+1) (.lit 0)).Exec p o (4+(pad+1)*6):=scan_exec S.bins (pad+1) (.lit 0) p trivial S.finish
  have pre:=prefix_run base slots pad shapes flags m early rows room
  have lens:=span_ge slots
  have prior : base+slots≤(ids base slots).base:=Nat.add_le_add_left lens base
  have start : (DescentStaticWordColumn.program w base (fun j=>j/shapes) slots).Exec m
      (head base slots shapes m) (4+10*slots):=DescentStaticWordColumn.mount base slots (fun j=>j/shapes) m (by omega)
  have addr:flags.base+slots≤(ids base slots).base:=((Nat.add_le_add_left rows _).trans early.2.2).trans (by omega)
  have exclusive : (ProtocolRAMEndpointPrefix.exclusive w flags.base (ids base slots).base slots).Exec
      (head base slots shapes m) p (10+(3+12*slots)):=ProtocolRAMEndpointPrefix.run flags.base (ids base slots).base slots
    (sumWords flags.base (head base slots shapes m)) (head base slots shapes m) addr cut rfl (fun i _=>by simp [sumWords])
  have upper:S.bins+(pad+1)≤endAddress base slots pad:=Nat.add_le_add_left (Nat.le_max_left ..) _
  refine ⟨by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then start (Procedure.Exec.then exclusive (Procedure.Exec.then wipe write))
      machine pc regs pubs exit rom advice cfg memory enter same,
    cheap_seq (DescentStaticWordColumn.cheap w base (fun j=>j/shapes) slots)
      (cheap_seq (ProtocolRAMRankCheap.exclusive_cheap w flags.base (ids base slots).base slots)
        (tally_cheap S k₀ v₀)),?_,?_⟩
  · rintro i (lo|hi)
    · exact (add_frame S k₀ v₀ tags wt o i (lo.trans_le low)).trans ((clear i (lo.trans_le low)).trans (pre.2 i (.inl lo)))
    · have after:=upper.trans hi
      exact (scatter_high S k₀ v₀ tags wt o i after).trans
        ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr after)).trans (pre.2 i (.inr (show S.first≤ i from bs.trans (by omega)))))
  · intro j
    change afterAdd S k₀ v₀ tags wt o (S.bins+j.val)=_
    rw [add_read,show o (S.bins+j.val)=0 from ProtocolRAMGeneratedWrite.read_image _ _ _ _ j,zero_add]

theorem invoice (room : endAddress base slots pad<2^w) :
    ticks base slots pad flags w room≤260*(1+slots+pad) := by
  have fee:=DescentParentBoundedKey.cost (banks base slots pad w room) flags (ids base slots) (codes base slots)
  change (10+(3+12*slots))+tallyCost (banks base slots pad w room) k₀ v₀≤240*(1+slots+pad) at fee
  unfold ticks
  omega

theorem hardware (room : endAddress base slots pad<2^w) :
    DescentStaticWordColumn.names (program base slots pad shapes flags w room)≤15*(slots+1)+2048 := by
  unfold program
  rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount]
  apply Nat.add_le_add_left
  have pref : DescentStaticWordColumn.names
      (ProtocolRAMEndpointPrefix.exclusive w flags.base (ids base slots).base slots)=38:=rfl
  have scatter (a b : ℕ) : DescentStaticWordColumn.names (ProtocolRAMIndexedWrite.scatter w a b slots)=
      DescentStaticWordColumn.names (ProtocolRAMIndexedWrite.scatter 1 0 0 0):=rfl
  have weighted (a : ℕ) : DescentStaticWordColumn.names (ProtocolRAMWeightedScatter.program w a slots)=
      DescentStaticWordColumn.names (ProtocolRAMWeightedScatter.program 1 0 0):=rfl
  simp only [tally,add,issue,ProtocolRAMGeneratedWrite.program,DescentStaticWordColumn.names_seq,
    DescentStaticWordColumn.names_scan,pref,scatter,weighted,slot,key,value,DescentParentBoundedKey.destination,Expr.work]
  decide

end
end Hierarchy.DescentResetParentDate

end OAI
