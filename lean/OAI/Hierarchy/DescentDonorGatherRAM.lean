import OAI.Hierarchy.DescentDonorWindow

namespace OAI
/-! # Native donor-window assembly, fixed lookup, and flat priced-register readback -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentPackedZip DescentSixParty ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H J M w : ℕ} (s : Shape)

structure Fields where
  raw : Expr
  signed : Expr
  owners : Expr
  ranks : Expr
  hub : Expr
  fresh : Expr

structure Tables6 where
  signed : Tables
  route : Tables
  fresh : Tables
  left : Tables
  all : Tables

def gather (T : Tables6) (e : Fields) :=
  T.all.read (T.left.read (T.signed.read e.raw e.signed) (T.route.read e.owners e.ranks)) (T.fresh.read e.hub e.fresh)

def clock (T : Tables6) (f : Fields) (H J M : ℕ) := 4+H*chunks J M*(2*(gather T f).work+4)

theorem work (t : Tables6) (f : Fields) :
    (gather t f).work = f.raw.work+f.signed.work+f.owners.work+f.ranks.work+f.hub.work+f.fresh.work+55 := by
  simp only [gather,Tables.read,Expr.work]
  omega

private def cat {a b : ℕ} (x : Cell a) (y : Cell b) := pair a b (x,y)

private theorem zero_cat (a b : ℕ) : cat (a:=a) (b:=b) 0 0=0 := by
  apply Fin.ext
  simp [cat,pair,finProdFinEquiv_apply_val]

structure FitsInputs (T : Tables6) (f : Fields) (M out w : ℕ) : Prop where
  ab : DescentPackedZip.Fits T.signed f.raw f.signed (rawBits s) (cableBits s) M out w
  cd : DescentPackedZip.Fits T.route f.owners f.ranks (ownerBits s) (chartBits s) M out w
  ef : DescentPackedZip.Fits T.fresh f.hub f.fresh (chartBits s) (freshBits s) M out w
  left : DescentPackedZip.Fits T.left (T.signed.read f.raw f.signed) (T.route.read f.owners f.ranks)
    (rawBits s+cableBits s) (ownerBits s+chartBits s) M out w
  final : DescentPackedZip.Fits T.all (T.left.read (T.signed.read f.raw f.signed) (T.route.read f.owners f.ranks))
    (T.fresh.read f.hub f.fresh) ((rawBits s+cableBits s)+(ownerBits s+chartBits s)) (chartBits s+freshBits s) M out w

structure Fixed (t : Tables6) (M : ℕ) (m : Memory w) : Prop where
  ab : Static t.signed (cat (a:=rawBits s) (b:=cableBits s)) M m
  cd : Static t.route (cat (a:=ownerBits s) (b:=chartBits s)) M m
  ef : Static t.fresh (cat (a:=chartBits s) (b:=freshBits s)) M m
  left : Static t.left (cat (a:=rawBits s+cableBits s) (b:=ownerBits s+chartBits s)) M m
  final : Static t.all (cat (a:=(rawBits s+cableBits s)+(ownerBits s+chartBits s)) (b:=chartBits s+freshBits s)) M m

structure Loaded (f : Fields) (x : Fin H→Fin J→Parts s) (M : ℕ) (m : Memory w) : Prop where
  terrain : Source f.raw (fun h j=>(x h j).terrain) M m
  cables : Source f.signed (fun h j=>(x h j).cables) M m
  owners : Source f.owners (fun h j=>(x h j).owners) M m
  ranks : Source f.ranks (fun h j=>(x h j).chart) M m
  hub : Source f.hub (fun h j=>(x h j).hub) M m
  births : Source f.fresh (fun h j=>(x h j).births) M m

theorem gathered (t : Tables6) (f : Fields) (out : ℕ) (room : FitsInputs s t f M out w)
    (x : Fin H→Fin J→Parts s) (m : Memory w) (rom : Fixed s t M m) (real : Loaded s f x M m) :
    Source (gather t f) (fun h j=>combine s (x h j)) M m := by
  have ab:=read_data _ _ _ _ room.ab _ (zero_cat _ _) m rom.ab _ _ real.terrain real.cables
  have cd:=read_data _ _ _ _ room.cd _ (zero_cat _ _) m rom.cd _ _ real.owners real.ranks
  have ef:=read_data _ _ _ _ room.ef _ (zero_cat _ _) m rom.ef _ _ real.hub real.births
  have one:=read_data _ _ _ _ room.left _ (zero_cat _ _) m rom.left _ _ ab cd
  exact read_data _ _ _ _ room.final _ (zero_cat _ _) m rom.final _ _ one ef

def program (t : Tables6) (f : Fields) (rom : Banks) (out H J M w : ℕ) :=
  (scan w rom.source.base (H*chunks J M) (gather t f)).seq (DescentSIMDLookup.program rom out H J M w)

def after (t : Tables6) (f : Fields) (rom : Banks) (out H J M : ℕ) (m : Memory w) :=
  image out (H*chunks J M) (DescentSIMDLookup.lookup rom) (image rom.source.base (H*chunks J M) (gather t f) m)

def clocks (t : Tables6) (f : Fields) (H J M : ℕ) := clock t f H J M + (4+44*(H*chunks J M))

theorem run (t : Tables6) (f : Fields) (rom : Banks) (out B profile b slots : ℕ)
    (fit : FitsInputs s t f M rom.source.base w)
    (finish : DescentSIMDLookup.Fits rom (totalBits s) (outputBits s) M H J w out)
    (x : Fin H→Fin J→Parts s) (m : Memory w) (common : Fixed s t M m) (sources : Loaded s f x M m)
    (literal : ∀pin : Cell (totalBits s*M) ⊕ Fin (H*chunks J M),∀bit : Fin w,
      wordBits w (m (fixedAddr rom pin)) bit=wordBits w (fixedWord (output s B profile b slots) pin) bit)
    (reside : rom.dictionary.base+rom.dictionary.size≤rom.source.base ∧ rom.mask.base+rom.mask.size≤rom.source.base) :
    let mem:=after t f rom out H J M m
    (program t f rom out H J M w).Exec m mem (clocks t f H J M) ∧
    (∀z : Row H J M,mem (out+(row H J M z).val)=((data (fun h j=>chip s B profile b slots (x h j)) z).val:Word w)) ∧
    (∀a,a<rom.source.base→mem a=m a) ∧ CheapCode (program t f rom out H J M w) := by
  intro mem
  let n:=H*chunks J M
  let mid:=image rom.source.base n (gather t f) m
  let goal:=output s B profile b slots
  have top : rom.source.base+n≤out := (Nat.add_le_add_left finish.srcSize _).trans finish.source.2.2
  have fits : (gather t f).Fits w rom.source.base := ⟨fit.final.apply,fit.final.right,fit.final.shift,fit.final.left⟩
  have gathered_:=gathered s t f rom.source.base fit x m common sources
  have loaded : PinFrame (M:=M) rom goal (fun h j=>combine s (x h j)) mid := by
    constructor
    · intro p bit
      rw [show mid (fixedAddr rom p)=m (fixedAddr rom p) from by
        have prior:fixedAddr rom p<rom.source.base := by
          cases p with
          | inl q=>
            have hq:q.val<rom.dictionary.size:=by simp [Bank.size,finish.dictBits]
            exact (Nat.add_lt_add_left hq _).trans_le reside.1
          | inr q=>exact (Nat.add_lt_add_left (q.isLt.trans_le finish.maskSize) _).trans_le reside.2
        simp [mid,image,fillSegment,Nat.not_le.mpr prior]]
      exact literal p bit
    · intro z
      have region:=(row H J M z).isLt
      simpa [mid,image,fillSegment,show rom.source.base≤rom.source.base+(row H J M z).val ∧
        rom.source.base+(row H J M z).val<rom.source.base+n by dsimp [n];omega,Nat.cast_add] using gathered_ z
  have exec_ : ((scan w rom.source.base n (gather t f)).seq
      (scan w out n (DescentSIMDLookup.lookup rom))).Exec m (image out n (DescentSIMDLookup.lookup rom) mid)
      ((4+n*(2*(gather t f).work+4))+(4+n*(2*(DescentSIMDLookup.lookup rom).work+4))) :=
    Procedure.Exec.then (scan_exec _ _ _ m fits (top.trans_lt (by have h:=finish.output;omega)))
    (scan_exec out n (DescentSIMDLookup.lookup rom) mid (by simp [DescentSIMDLookup.lookup,Expr.Fits,finish.source,finish.mask,finish.dictionary]) finish.output)
  refine ⟨?_,?_,?_,cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)⟩
  · rw [lookup_work] at exec_
    unfold program clocks clock DescentSIMDLookup.program
    rw [show 44*(H*chunks J M)=(H*chunks J M)*(2*20+4) by omega]
    exact @exec_
  · intro z
    simpa only [mem,after,mid,n,goal,output,separate_combine] using PackedCensus.col_read rom out finish goal _ mid loaded z
  · intro a low
    have both:a<out:=low.trans_le ((Nat.le_add_right ..).trans top)
    simp [mem,after,image,fillSegment,Nat.not_le.mpr both,Nat.not_le.mpr low]

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
