import OAI.Hierarchy.DescentSeedCensusStamp

import OAI.Hierarchy.DescentSeedWideBundleRead
import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # A single fixed packed lookup scan writes all internal primitive seed labels -/
namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot DescentInitialHost DescentSixParty DescentPrimitivePalette DescentEpochTagKeys DescentSIMDLookup Catalyst
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k p w s R : ℕ} (X : Approximation F k p)
local notation "H" => Fintype.card (Old X)
local notation "d" => digitsNeeded s
local notation "inputBits" => d*8
local notation "b" => roleBits s
local notation "M" => pieces w s
local notation "n" => H*chunks R M

theorem shelf_read {n' : ℕ} (start : ℕ) (f : Fin n'→ℕ) (m : Memory w) (i : Fin n') :
    shelf start n' f m (start+i.val)=(f i:Word w):=by simp [shelf,i.isLt]

theorem shelf_keep {n' : ℕ} (start : ℕ) (f : Fin n'→ℕ) (m : Memory w) (i : ℕ) (before : i<start) :
    shelf start n' f m i=m i:=by simp [shelf,show ¬start ≤ i by omega]

namespace Spaced
variable {laneCount : ℕ}
local notation "rows₀" => H*chunks R laneCount

structure Static (T : Tape) (m : Memory w) : Prop where
  tag (p : Row H R laneCount) : m (T.classes.base+(row H R laneCount p).val)=(offset s laneCount (sitePlan X p.1):Word w)
  mask (p : Row H R laneCount) : m (T.mask.base+(row H R laneCount p).val)=(maskWord b laneCount R p.2.val:Word w)
  table (P : Plan) (key : Cell (inputBits*laneCount)) : m (T.dict.base+(offset s laneCount P+key.val))=
    ((DescentSIMDLookup.table (entry s P) key).val:Word w)

theorem static_read (start src : ℕ) (prior : Memory w) :
    Static (laneCount:=laneCount) (s:=s) (R:=R) X (tape start H R laneCount s src) (stamp (laneCount:=laneCount) (R:=R) (s:=s) X start prior) := by
  constructor
  · intro p
    have hi:=(row H R laneCount p).isLt
    unfold stamp
    rw [shelf_keep _ _ _ _ (by change start+cols s laneCount+(row H R laneCount p).val<_;omega)]
    simpa [tape] using shelf_read (start+cols s laneCount) (fun i=>offset s laneCount (sitePlan X ((row H R laneCount).symm i).1))
      (shelf start (cols s laneCount) (dictWord s laneCount) prior) (row H R laneCount p)
  · intro p
    unfold stamp
    simp only [tape,shelf_read,Equiv.symm_apply_apply]
  · intro P key
    let i : Fin (cols s laneCount):=finProdFinEquiv (plans P,key)
    have atI:i.val=offset s laneCount P+key.val:=by simp [i,offset,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
    have hi:=i.isLt
    change stamp (laneCount:=laneCount) (R:=R) (s:=s) X start prior (start+(offset s laneCount P+key.val))=_
    rw [←atI];unfold stamp
    rw [shelf_keep _ _ _ _ (by omega),shelf_keep _ _ _ _ (by omega),shelf_read]
    simp [i,dictWord]

theorem retained (start _src : ℕ) (old : Memory w) (a : ℕ) (ha : a<start) :
    stamp (laneCount:=laneCount) (s:=s) (R:=R) X start old a=old a := by
  unfold stamp
  rw [shelf_keep _ _ _ _ (by omega),shelf_keep _ _ _ _ (by omega),shelf_keep _ _ _ _ ha]

theorem read (T : Tape) (out : ℕ) (fit : Room T out inputBits b laneCount H R s w) (mem : Memory w)
    (data_ : Fin H→Fin R→Cell inputBits) (haveOld : ∀p : Row H R laneCount,mem (T.source.base+(row H R laneCount p).val)=((data data_ p).val:Word w))
    (fixed : Static (laneCount:=laneCount) (R:=R) (s:=s) X T mem) (p : Row H R laneCount) :
    (spread T).eval mem ((row H R laneCount p).val:Word w)=
      ((data (fun v j=>entry s (sitePlan X v) (data_ v j)) p).val:Word w) := by
  let P:=sitePlan X p.1
  let key:=data data_ p
  let y:=table (entry s P) key
  have address : offset s laneCount P+key.val<cols s laneCount:=by
    have slack:=Nat.mul_le_mul_right (2^(inputBits*laneCount)) (plans P).isLt
    rw [Nat.succ_mul] at slack
    change (plans P).val*2^(inputBits*laneCount)+key.val<Fintype.card Plan*2^(inputBits*laneCount)
    have:=key.isLt;omega
  let index := (row H R laneCount p).val
  have rowRead (B : Bank) (inList : B∈[T.source,T.mask,T.classes]) :
      B.read mem (index:Word w)=mem (B.base+index) := by
    have full : B∈[T.source,T.mask,T.classes,T.dict] := List.mem_append_left [T.dict] inList
    exact DescentPackedZip.bank_read B mem ((row H R laneCount p).isLt.trans_le (fit.rows B inList))
      (fit.fits B full)
  have tagRead : T.classes.read mem (index:Word w)=(offset s laneCount P:Word w) :=
    (rowRead _ (by simp)).trans (fixed.tag p)
  have keyRead : T.source.read mem (index:Word w)=(key.val:Word w) :=
    (rowRead _ (by simp)).trans (haveOld p)
  have coord : T.classes.read mem (index:Word w)+T.source.read mem (index:Word w)=
      ((offset s laneCount P+key.val:ℕ):Word w) := by rw [tagRead,keyRead,Nat.cast_add]
  have dictRead : T.dict.read mem ((offset s laneCount P+key.val:ℕ):Word w)=(y.val:Word w) :=
    (DescentPackedZip.bank_read T.dict mem (address.trans_le fit.dict) (fit.fits _ (by simp))).trans
      (fixed.table P key)
  have maskRead : T.mask.read mem (index:Word w)=(maskWord b laneCount R p.2.val:Word w) :=
    (rowRead _ (by simp)).trans (fixed.mask p)
  have maskBound : maskWord b laneCount R p.2.val<2^w := by
    have bound : b*used R laneCount p.2.val≤w := (Nat.mul_le_mul_left _ (Nat.min_le_left ..)).trans fit.result
    have upper := Nat.pow_le_pow_right (by decide : 0<2) bound
    have pos := Nat.two_pow_pos (b*used R laneCount p.2.val)
    unfold maskWord
    omega
  have fitsY : y.val<2^w := y.isLt.trans_le (Nat.pow_le_pow_right (by decide) fit.result)
  have bits : y.val &&& maskWord b laneCount R p.2.val=masked (entry s P) data_ p :=
    Nat.and_two_pow_sub_one_eq_mod _ _
  have lanes {a c hosts rows lanes : ℕ} (f : Fin hosts→Cell a→Cell c) (x : Fin hosts→Fin rows→Cell a)
      (z : Row hosts rows lanes) :
      data (fun v j=>f v (x v j)) z=data (fun v j=>f z.1 (x v j)) z := by
    simp only [data]
  have atHost := lanes (fun v=>entry s (sitePlan X v)) data_ p
  calc
    _ = (masked (entry s P) data_ p:Word w) := by
      change (((T.dict.read mem (T.classes.read mem (index:Word w)+T.source.read mem (index:Word w))).val
        &&& (T.mask.read mem (index:Word w)).val:ℕ):Word w)=_
      rw [coord,dictRead,maskRead,Fin.val_cast_of_lt fitsY,Fin.val_cast_of_lt maskBound,bits]
    _ = _ := congrArg (fun x:ℕ=>(x:Word w)) ((DescentSixParty.PackedCensus.masked_data (entry s P) data_ p).trans
      (congrArg Fin.val atHost.symm))

theorem native (start out : ℕ) (sel : Select X R s→Bool) (mem : Memory w)
    (earlier : publicWords X+H*chunks R laneCount ≤ start)
    (old : ∀p : Row H R laneCount,mem (publicWords X+(row H R laneCount p).val)=
      ((data (bundles X sel) p).val:Word w))
    (fit : Room (tape start H R laneCount s (publicWords X)) out inputBits b laneCount H R s w) :
    let T:=tape start H R laneCount s (publicWords X)
    let init:=stamp (laneCount:=laneCount) (s:=s) (R:=R) X start mem
    let dst:=image out rows₀ (spread T) init
    (scan w out rows₀ (spread T)).Exec init dst (4+60*rows₀) ∧
      (∀p : Row H R laneCount,dst (out+(row H R laneCount p).val)=
        ((data (fun v j=>entry s (sitePlan X v) (bundles X sel v j)) p).val:Word w)) ∧
      (∀i<out,dst i=init i) ∧ CheapCode (scan w out rows₀ (spread T)) := by
  intro T init dst
  have source (p : Row H R laneCount) :
      init (T.source.base+(row H R laneCount p).val)=((data (bundles X sel) p).val:Word w):=
    (retained (laneCount:=laneCount) (s:=s) (R:=R) X start (publicWords X) mem _ ((Nat.add_lt_add_left (row H R laneCount p).isLt _).trans_le earlier)).trans (old p)
  have banksFit (banks : Tape)
      (allFit : ∀ bank∈[banks.source,banks.mask,banks.classes,banks.dict],bank.Fits w out) :
      (spread banks).Fits w out :=
    ⟨⟨allFit _ (by simp),⟨⟨allFit _ (by simp),trivial⟩,⟨allFit _ (by simp),trivial⟩⟩⟩,
      ⟨allFit _ (by simp),trivial⟩⟩
  refine ⟨?_,?_,?_,@scan_cheap _ _ _ _⟩
  · have cost : 4+rows₀*(2*(spread T).work+4) = 4+60*rows₀ := by rw [work]; ring
    rw [←cost]
    exact @scan_exec w out rows₀ (spread T) init (banksFit T fit.fits) fit.output
  · intro p
    rw [show dst=image out rows₀ (spread T) init from rfl,ProtocolRAMGeneratedWrite.read_image]
    exact read X T out fit init (bundles X sel) source (static_read (laneCount:=laneCount) X start (publicWords X) mem) p
  · intro i hi;exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hi)

end Spaced
end
end Hierarchy.DescentPackedSeed.Primitive

end OAI
