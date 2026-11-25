import OAI.Hierarchy.DescentPackedMatchFlatWords

namespace OAI
/-! # A complete packed matching pass from the physically read neighborhood fields -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentPackedProfileWindow
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w K H G M R r D p d : ℕ}

structure Header (s : Shape) (M R H G : ℕ) (g : Banks) (l : ProfileTable.Layout)
    (stream : ℕ→Cell s.digit) (m : Memory w) : Prop where
  lookup : resident s g H G M m
  sums : ∀k : Cell (s.outputBits*M),m (l.countROM.base+k.val)=(chunkCount s M k:Word w)
  fixed : ProfileTable.static s M R l.tables m
  tape : ∀i<l.raw.size,m (l.raw.base+i)=((DescentPackedProfileWindow.word s.digit R stream i).val:Word w)

structure FixedBefore (w cut : ℕ) (g : Banks) (l : ProfileTable.Layout) : Prop where
  look : g.dictionary.Fits w cut
  masks : g.mask.Fits w cut
  sums : l.countROM.Fits w cut
  top : l.tables.topology.Fits w cut
  off : l.tables.offset.Fits w cut
  low : l.tables.low.Fits w cut
  last : l.tables.result.Fits w cut
  tape : l.raw.Fits w cut

theorem Header.below {s : Shape} {M R H G cut : ℕ} {g : Banks} {l : ProfileTable.Layout}
    {stream : ℕ→Cell s.digit} {m o : Memory w} (h : Header s M R H G g l stream m)
    (early : FixedBefore w cut g l) (frame : ∀a<cut,o a=m a)
    (fit : DescentSIMDLookup.Fits g s.inputBits s.outputBits M H G w l.topology.base)
    (room : ProfileTable.Room s M R (H*chunks G M) w l) : Header s M R H G g l stream o := by
  have get {b : Bank} (low : b.Fits w cut) (i : ℕ) (hi : i<b.size) :=
    frame (b.base+i) ((Nat.add_lt_add_left hi _).trans_le low.2.2)
  have bitget {b : Bank} {d : ℕ} (low : b.Fits w cut) (bits : b.bits=d) (i : Cell d) :=
    get low i.val (by simpa only [Bank.size,bits] using i.isLt)
  exact ⟨⟨fun i=>(bitget early.look fit.dictBits i).trans (h.lookup.1 i),
    fun p=>(get early.masks p.val (p.isLt.trans_le fit.maskSize)).trans (h.lookup.2 p)⟩,
    fun i=>(bitget early.sums room.countBits i).trans (h.sums i),
    ⟨fun i=>(bitget early.top room.scan.keyT i).trans (h.fixed.1 i),
     fun i=>(bitget early.off room.scan.keyO i).trans (h.fixed.2.1 i),
     fun i=>(bitget early.low room.scan.keyL i).trans (h.fixed.2.2.1 i),
     fun i=>(bitget early.last room.scan.keyR i).trans (h.fixed.2.2.2 i)⟩,
    fun i hi=>(get early.tape i hi).trans (h.tape i hi)⟩

def complete (w R : ℕ) (tables : Fin (fields r D p)→DescentPackedZip.Tables) (field : Fin (fields r D p)→Expr)
    (dict : Fin K→Bank) (mask : Bank) (H G M : ℕ) (g : Banks) (l : ProfileTable.Layout) :=
  (all w tables field dict mask g.source.base H G M).seq (full w R (K*H) G M g l)

theorem complete_run (s : Shape) (B : ℕ) (tables : Fin (fields r D p)→DescentPackedZip.Tables)
    (field : Fin (fields r D p)→Expr) (dict : Fin K→Bank) (mask : Bank) (g : Banks) (l : ProfileTable.Layout)
    (u : Fin H→Fin G→Panel r D p d) (m : Memory w) (stream : ℕ→Cell s.digit)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field g.source.base)
    (static : ∀i,DescentPackedZip.Static (tables i) (setField (d:=d) i) M m)
    (source : ∀i,DescentPackedZip.Source (field i) (fun h j=>terrain u h j i) M m)
    (df : ∀key,(dict key).Fits w g.source.base) (mf : mask.Fits w g.source.base)
    (bits : ∀key,(dict key).bits=(d*fields r D p)*M) (span : H*chunks G M≤ mask.size)
    (fixed : ∀key : Fin K,∀i : Cell ((d*fields r D p)*M),m ((dict key).base+i.val)=
      ((DescentSIMDLookup.table (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key.val) i).val:Word w))
    (masks : ∀t : Row H G M,m (mask.base+(row H G M t).val)=(maskWord s.inputBits M G t.2.val:Word w))
    (fit : DescentSIMDLookup.Fits g s.inputBits s.outputBits M (K*H) G w l.topology.base)
    (room : ProfileTable.Room s M R ((K*H)*chunks G M) w l) (prior : Earlier w l)
    (original : Header s M R (K*H) G g l stream m) (early : FixedBefore w g.source.base g l)
    (pos : 0<R) (size : M*s.pairs≤R) (double : 2*R≤2^w) (digits : R≤2^(s.digit*R))
    (windowRoom : ∀i : Fin ((K*H)*chunks G M),
      PackedProfileCursor.total (ProfileTable.quota (M:=M) s (topologyWords (M:=M) s (flat (descriptorInputs (K:=K) s B u)))) i.val/R+1<l.raw.size) :
    let n:=(K*H)*chunks G M
    let ps:=passes tables field dict mask g.source.base H G M
    let keys:=topologyWords (M:=M) s (flat (descriptorInputs (K:=K) s B u))
    let o:=finished R (K*H) G M g l (ProtocolRAM.result ps m)
    (complete w R tables field dict mask H G M g l).Exec m o (clock ps+((4+44*n)+ProfileTable.clock n)) ∧
      (∀i : Fin n,o (l.topology.base+i.val)=((keys i).val:Word w)) ∧
      (∀i : Fin n,∀a : Fin M,∀j : Fin s.pairs,
        digit s.digit (finProdFinEquiv (a,j)).val (o (l.out+i.val)).val=
        if j.val<(laneCounts s M (keys i) a).val then
          (stream (PackedProfileCursor.total (ProfileTable.quota s keys) i.val+localPrefix (laneCounts s M (keys i)) a+j.val)).val else 0) ∧
      (∀a<g.source.base,o a=m a) ∧ CheapCode (complete w R tables field dict mask H G M g l) := by
  have total : g.source.base+K*(H*chunks G M)<2^w := by
    have cap:=fit.srcSize
    rw [Nat.mul_assoc] at cap
    exact (Nat.add_le_add_left cap _).trans_lt (fit.source.2.2.trans_lt ((Nat.le_add_right ..).trans_lt fit.output))
  have width : s.inputBits*M≤w := by
    have h:=Nat.mul_le_mul_left M (le_max_left s.inputBits s.outputBits)
    rw [Nat.mul_comm M s.inputBits] at h
    exact (h.trans fit.packed).trans (Nat.div_le_self ..)
  obtain ⟨assembly,words,unchanged,cheap_⟩:=all_flat tables field g.source.base s B dict mask u m bounds static source df mf bits span
    total width fixed masks
  have h:=original.below early unchanged fit room
  obtain ⟨emit,records,profiles,keeps⟩:=full_run s g l fit room prior (flat (descriptorInputs (K:=K) s B u)) _ stream
    h.lookup words pos size double digits h.sums h.fixed h.tape windowRoom
  exact ⟨Procedure.Exec.then assembly emit,records,profiles,fun a ha=>(keeps a (ha.trans_le ((Nat.le_add_right ..).trans fit.source.2.2))).trans
    (unchanged a ha),@cheap_seq w (all w tables field dict mask g.source.base H G M) (full w R (K*H) G M g l)
      cheap_ (@full_cheap w R (K*H) G M g l)⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather

end OAI
