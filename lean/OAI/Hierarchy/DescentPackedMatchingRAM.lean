import OAI.Hierarchy.DescentPackedMatchingTable
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # One word-RAM lookup per packed row of bounded matching neighborhoods -/

namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M : ℕ} (s : Shape)

def literal (M w : ℕ) (i : Cell (s.inputBits*M)) : Word w := (table (lookupCell s) i).val

/-- A fixed immutable header interval, with the padding masks immediately after its dictionary. -/
def banks (source : Bank) (lo maskBits M : ℕ) : Banks :=
  ⟨source,⟨lo,s.inputBits*M⟩,⟨lo+2^(s.inputBits*M),maskBits⟩⟩

def header (H G M w lo : ℕ) (m : Memory w) (addr : ℕ) : Word w :=
  let D:=2^(s.inputBits*M)
  let N:=H*chunks G M
  if _left : addr<lo then m addr else
    if dict : addr-lo<D then literal s M w ⟨_,dict⟩ else
      if p : addr-(lo+D)<N then (maskWord s.outputBits M G ((row H G M).symm ⟨_,p⟩).2.val:ℕ) else m addr

theorem header_dictionary (H G M w lo : ℕ) (m : Memory w) (i : Cell (s.inputBits*M)) :
    header s H G M w lo m (lo+i.val)=literal s M w i := by simp [header,Nat.not_lt.mpr (Nat.le_add_right lo i.val),i.isLt]

theorem header_mask (H G M w lo : ℕ) (m : Memory w) (i : Fin (H*chunks G M)) :
    header s H G M w lo m (lo+2^(s.inputBits*M)+i.val)=
      (maskWord s.outputBits M G ((row H G M).symm i).2.val:Word w) := by
  have h : ¬lo+2^(s.inputBits*M)+i.val<lo :=
    Nat.not_lt_of_le ((Nat.le_add_right lo _).trans (Nat.le_add_right _ i.val))
  have k : lo+2^(s.inputBits*M)+i.val-lo=2^(s.inputBits*M)+i.val := by
    rw [Nat.add_assoc,Nat.add_sub_cancel_left]
  have past : ¬2^(s.inputBits*M)+i.val<2^(s.inputBits*M) :=
    Nat.not_lt_of_le (Nat.le_add_right _ _)
  simp [header,h,k,past,i.isLt]

def resident (g : Banks) (H G M : ℕ) (m : Memory w) : Prop :=
  (∀i : Cell (s.inputBits*M),m (g.dictionary.base+i.val)=literal s M w i) ∧
    ∀p : Fin (H*chunks G M),m (g.mask.base+p.val)=(maskWord s.outputBits M G ((row H G M).symm p).2.val:Word w)

theorem resident_header (source : Bank) (lo mb H G M w : ℕ) (m : Memory w) :
    resident s (banks s source lo mb M) H G M (header s H G M w lo m) :=
  ⟨header_dictionary s H G M w lo m,header_mask s H G M w lo m⟩

def physical (g : Banks) (out H G M w : ℕ) := DescentSIMDLookup.program g out H G M w

def result (g : Banks) (out H G M : ℕ) (m : Memory w) := image out (H*chunks G M) (lookup g) m

theorem execute (g : Banks) (out : ℕ) (fit : Fits g s.inputBits s.outputBits M H G w out)
    (x : Fin H→Fin G→Inputs s) (m : Memory w) (ready : resident s g H G M m)
    (source : ∀p : Row H G M,m (g.source.base+(row H G M p).val)=
      ((data (fun h j=>encodeInput (x h j)) p).val:Word w)) :
    (physical g out H G M w).Exec m (result g out H G M m) (4+44*(H*chunks G M)) ∧
    (∀p : Row H G M,result g out H G M m (out+(row H G M p).val)=
      (masked (lookupCell s) (fun h j=>encodeInput (x h j)) p:Word w)) ∧
    ∀a<out,result g out H G M m a=m a := by
  let input := fun h j=>encodeInput (x h j)
  have inputFrame : PinFrame (M:=M) g (lookupCell s) input m := by
    refine ⟨?_,source⟩
    intro key bit
    cases key with
    | inl key=>exact congrArg (fun n=>wordBits w n bit) (ready.1 key)
    | inr key=>exact congrArg (fun n=>wordBits w n bit) (ready.2 key)
  have ok : (lookup g).Fits w out := ⟨⟨fit.dictionary,fit.source,trivial⟩,fit.mask,trivial⟩
  have run : (scan w out (H*chunks G M) (lookup g)).Exec m (result g out H G M m)
      (4+(H*chunks G M)*(2*(lookup g).work+4)) := scan_exec out (H*chunks G M) (lookup g) m ok fit.output
  have clock : 4+44*(H*chunks G M) = 4+(H*chunks G M)*(2*(lookup g).work+4) := by
    rw [lookup_work,Nat.mul_comm 44]
  refine ⟨?_,?_,
    fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha)⟩
  · rw [clock]
    exact @run
  · intro p
    exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (lookup_read g out fit (lookupCell s) input m inputFrame p)

theorem stored_lane (g : Banks) (out : ℕ) (fit : Fits g s.inputBits s.outputBits M H G w out)
    (x : Fin H→Fin G→Inputs s) (o : Memory w)
    (read : ∀p : Row H G M,o (out+(row H G M p).val)=
      (masked (lookupCell s) (fun h j=>encodeInput (x h j)) p:Word w))
    (v : Fin H) (j : Fin G) (positive : 0<M) :
    digit s.outputBits (lane j positive).val (o (out+(row H G M (position v j positive)).val)).val=
      (encodeOutput (transform (x v j))).val := by
  simpa only [lookupCell,decode_encode] using
    physical_read g out fit (lookupCell s) (fun h g=>encodeInput (x h g)) o read v j positive

/-- The table key uses the payload width, while real scan ticks are charged at
the physical address width. Their ratio is the stated factor in the invoice. -/
theorem bit_price (H G payload W ratio : ℕ) (positive : 0<s.bits) (wide : 2*s.bits≤payload)
    (compare : W≤ratio*payload) :
    let L:=lanes payload s.bits
    (4+44*(H*chunks G L))*W ≤ ratio*(4*payload+44*(H*payload+4*H*G*s.bits)) ∧
      (2^(s.inputBits*L)+3*(H*chunks G L))*W ≤ ratio*(2^(payload/2)*payload+3*(H*payload+4*H*G*s.bits)) := by
  let L:=lanes payload s.bits
  have vol := DescentSIMDLookup.volume H G payload s.bits positive wide
  have rom := DescentSIMDLookup.rom_entries s.inputBits s.outputBits payload
  change 2^(s.inputBits*L)≤2^(payload/2) at rom
  have pay : (4+44*(H*chunks G L))*payload≤4*payload+44*(H*payload+4*H*G*s.bits) := by
    nlinarith only [vol]
  have area : (2^(s.inputBits*L)+3*(H*chunks G L))*payload≤2^(payload/2)*payload+3*(H*payload+4*H*G*s.bits) := by
    nlinarith only [vol,Nat.mul_le_mul_right payload rom]
  constructor
  · exact (Nat.mul_le_mul_left _ compare).trans (by simpa only [mul_left_comm] using Nat.mul_le_mul_left ratio pay)
  · exact (Nat.mul_le_mul_left _ compare).trans (by simpa only [mul_left_comm] using Nat.mul_le_mul_left ratio area)

theorem cheap (g : Banks) (out H G M w : ℕ) : CheapCode (physical g out H G M w) := @scan_cheap _ _ _ _

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
