import OAI.Hierarchy.DescentOrdinaryVenueClipNumbers
import OAI.Hierarchy.DescentScalarVenueHeaders
import OAI.Hierarchy.DescentScalarVenueFields
import OAI.Hierarchy.DescentZipBook

namespace OAI
/-! # Physical scalar-venue receiver from the prior actor route banks -/
namespace Hierarchy.DescentScalarVenueMask.Receiver
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentPackedColony DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M P r cap k gain raw slots low w : ℕ}
local notation "A"=>DescentPackedActorMask.actors (P*r) cap
local notation "K"=>1+cap*6
local notation "a"=>Packed.bits low
local notation "b"=>Packed.bits raw

abbrev Tag (n : ℕ):=Fin 2⊕Fin n

def gate (k gain slots raw low n : ℕ) : Tag n→Book.Gate
  | .inl s=>if s=0 then ⟨1,Packed.bits raw,Packed.bits raw,keepRaw⟩ else ⟨1,Packed.bits raw,Packed.bits low,trimmed k gain slots raw low⟩
  | .inr j=>⟨Packed.bits low*n,Packed.bits low,Packed.bits low*n,Gather.setField j⟩

def entries (k gain slots raw low n : ℕ) (i : Fin (2+n)):=gate k gain slots raw low n (finSumFinEquiv.symm i)
def length (raw low M n : ℕ):=(2+n)*(2*2^(unit raw low n*M))
def header (base raw low M n : ℕ):=base+length raw low M n

def view (ports : Ports P) (route key : Fin r→Fin K→Bank) (hub : Bank) (k gain slots raw low M H G base : ℕ) : Donors P r cap:={
  ports,route, localKey:=key,hub:=.lookup hub .row,
  head:=fun s=>⟨Headers.layout (header base raw low M A) H G M P s,
    Book.tables (entries k gain slots raw low A) (unit raw low A) M base (finSumFinEquiv (.inl (0 : Fin 2))),
    Book.tables (entries k gain slots raw low A) (unit raw low A) M base (finSumFinEquiv (.inl (1 : Fin 2)))⟩,
  masks:=fun j=>Book.tables (entries k gain slots raw low A) (unit raw low A) M base (finSumFinEquiv (.inr j)) }

theorem width (k gain slots raw low n : ℕ) (i : Fin (2+n)) : let g:=entries k gain slots raw low n i;g.left+g.right≤unit raw low n:=by
  unfold entries;cases (finSumFinEquiv.symm i : Tag n) with
  | inl s=>by_cases h:s=0 <;> simp [gate,h,unit]
  | inr z=>exact le_max_right ..

structure Raw (ports : Ports P) (route key : Fin r→Fin K→Bank) (hub ends : Bank) (base : ℕ)
    (walks : Fin H→Fin P→Option (Fin H)) (t : Fin r→Fin K→Fin H→Fin G→Ticket P raw) (hubs : Fin H→Fin G→Cell 1) (M : ℕ) (m : Memory w) : Prop where
  routed : Mounted ports (DescentSortedRoster.indexed walks) m G M
  shape : Accessible ports hub H G M w base
  endsFit : ends.Fits w base
  endsRoom : H*P≤ends.size
  endsRead : ∀h p,m (ends.base+(h.val*P+p.val))=(DescentScalarVenueDirectory.number (walks h p):Word w)
  routeFit : ∀x s,(route x s).Fits w base
  routeRoom : ∀x s,H*chunks G M≤(route x s).size
  routeRead : ∀x s,Reads (route x s) (fun h g=>pathCode (t x s h g)) M m
  keyFit : ∀x s,(key x s).Fits w base
  keyRoom : ∀x s,H*chunks G M≤(key x s).size
  keyRead : ∀x s,Reads (key x s) (fun h g=>localCode (t x s h g)) M m
  hubsRead : Reads hub hubs M m

theorem readable {T : Tables} {x y : Expr} {l r M out w : ℕ} (fit : DescentPackedZip.Fits T x y l r M out w) : (T.read x y).Fits w out:=
  ⟨fit.apply,fit.right,fit.shift,fit.left⟩

private theorem indexRoom (h : Fin H) (p : Fin P):h.val*P+p.val<H*P:=(Nat.add_lt_add_left p.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)

/-- Only live old inputs are needed at entry. Return lookup, truncation,
masking and component insertion share one bank of fixed shape pages. -/
theorem mount (ports : Ports P) (route key : Fin r→Fin K→Bank) (hub ends : Bank) (k gain slots low base : ℕ)
    (walks : Fin H→Fin P→Option (Fin H)) (t : Fin r→Fin K→Fin H→Fin G→Ticket P raw) (hubs : Fin H→Fin G→Cell 1) (m : Memory w)
    (old : Raw ports route key hub ends base walks t hubs M m)
    (hi : Headers.post (header base raw low M A) H G M P+H*chunks G M<2^w) :
    let f:=entries k gain slots raw low A;let u:=unit raw low A;let start:=header base raw low M A;let out:=Headers.post start H G M P
    let mid:=Book.image f u M base m;let end_:=Headers.image ports.roster ends start H G M P mid;let C:=view ports route key hub k gain slots raw low M H G base
    ((Book.install f u M w base).seq (Headers.code ports.roster ends start H G M P w)).Exec m end_ ((4+10*length raw low M A)+Headers.ticks ports.roster ends start H G M P) ∧
      MountedDonors C walks t hubs k gain slots low M out end_ ∧ (∀x,x<base ∨ out≤x→end_ x=m x) ∧
        CheapCode ((Book.install f u M w base).seq (Headers.code ports.roster ends start H G M P w)):=by
  intro f u start out mid end_ C
  have next : start ≤ out := calc
    start ≤ Headers.start start H P := Nat.le_add_right _ _
    _ ≤ Headers.afterHeaders start H P := Nat.le_add_right _ _
    _ ≤ Headers.rom start H P := Nat.le_add_right _ _
    _ ≤ Headers.rom start H P + DescentPackedChildNeighbor.SIMD.ROM.cells P (Packed.bits P) 1 M H G :=
      Nat.le_add_right _ _
    _ ≤ out := Nat.le_add_right _ _
  have before:base≤ start:=Nat.le_add_right ..;have early:=before.trans next;have endFit:out<2^w:=(Nat.le_add_right ..).trans_lt hi
  have liftB {x y : ℕ} (h:x≤y) (B:Bank) (ok:B.Fits w x):B.Fits w y:=⟨ok.1,ok.2.1,ok.2.2.trans h⟩
  obtain ⟨init,dict,fr,cost⟩:=Book.mount f u M base m (width k gain slots raw low A) (next.trans_lt endFit)
  have retained {B:Bank} {i:ℕ} (ok:B.Fits w base) (index:i<B.size):mid (B.base+i)=m (B.base+i):=fr _ (.inl ((Nat.add_lt_add_left index _).trans_le ok.2.2))
  have rank (h:Fin H) (s:Fin P):mid (ports.roster.base+(h.val*P+s.val))=(DescentScalarVenueDirectory.number (DescentSortedRoster.indexed walks h s):Word w):=
    (retained old.shape.roster ((indexRoom h s).trans_le old.shape.rosterRoom)).trans (old.routed.roster h s)
  have ends_ (h:Fin H) (p:Fin P):mid (ends.base+(h.val*P+p.val))=(DescentScalarVenueDirectory.number (walks h p):Word w):=
    (retained old.endsFit ((indexRoom h p).trans_le old.endsRoom)).trans (old.endsRead h p)
  obtain ⟨headers,queries,queryFit,rest,cheap⟩:=Headers.mount ports.roster ends start mid walks (liftB before _ old.shape.roster) (liftB before _ old.endsFit)
    old.shape.rosterRoom old.endsRoom rank ends_ hi
  have intact (j : ℕ) (away:j<base ∨ out≤j):end_ j=m j:=by
    rcases away with lower|upper
    · exact (rest _ (.inl (lower.trans_le before))).trans (fr _ (.inl lower))
    · exact (rest _ (.inr upper)).trans (fr _ (.inr (next.trans upper)))
  have fixed:=Book.retained f u M base end_ mid (width k gain slots raw low A) dict (fun x _ h=>rest x (.inl h))
  have fixedTag (tag : Tag A) (g : Book.Gate) (selected : gate k gain slots raw low A tag = g) :
      Static (Book.tables f u M base (finSumFinEquiv tag)) g.eval M end_ := by
    have entry : f (finSumFinEquiv tag) = g :=
      (congrArg (gate k gain slots raw low A) (finSumFinEquiv.symm_apply_apply tag)).trans selected
    exact (congrArg (fun q : Book.Gate =>
      Static (Book.tables f u M base (finSumFinEquiv tag)) q.eval M end_) entry).mp
      (fixed (finSumFinEquiv tag))
  have geom (i : Fin (2+A)):=Book.geometry f u M base i next endFit (width k gain slots raw low A i)
  have atBank {B:Bank} {j:ℕ} (ok:B.Fits w base) (c:j<B.size):end_ (B.base+j)=m (B.base+j):=intact _ (.inl ((Nat.add_lt_add_left c _).trans_le ok.2.2))
  have reads {bits : ℕ} (B:Bank) (x:Fin H→Fin G→Cell bits) (cap_:H*chunks G M≤B.size) (fit:B.Fits w base) (seen:Reads B x M m):Reads B x M end_:=
    fun p=>(atBank fit ((row H G M p).isLt.trans_le cap_)).trans (seen p)
  have access (B:Bank) (cap_:H*chunks G M≤B.size) (fit:B.Fits w base):Accessible ports B H G M w out:=
    ⟨fun j=>liftB early _ (old.shape.ids j),old.shape.idsRoom,liftB early _ old.shape.roster,old.shape.rosterRoom,liftB early _ old.shape.offsets,old.shape.offRoom,
    liftB early _ old.shape.chunks,old.shape.chunkRoom,liftB early B fit,cap_⟩
  have mounted : Mounted ports (DescentSortedRoster.indexed walks) end_ G M:=
    ⟨fun p j=>(atBank (old.shape.ids j) ((row H G M p).isLt.trans_le (old.shape.idsRoom j))).trans (old.routed.ids p j),
    fun h j=>(atBank old.shape.roster ((indexRoom h j).trans_le old.shape.rosterRoom)).trans (old.routed.roster h j),
    fun h=>(atBank old.shape.offsets (h.isLt.trans_le old.shape.offRoom)).trans (old.routed.offsets h),
    fun p=>(atBank old.shape.chunks ((row H G M p).isLt.trans_le old.shape.chunkRoom)).trans (old.routed.chunks p)⟩
  have reg (s : Fin P) (x : Fin r) (j : Fin K) :=(queryFit s _ (peer_fits ports (route x j) out (access _ (old.routeRoom x j) (old.routeFit x j)) s))
  have low_ (s : Fin P) (x : Fin r) (j : Fin K) :=(peer_fits ports (key x j) out (access _ (old.keyRoom x j) (old.keyFit x j)) s)
  have hf : (Expr.lookup hub .row).Fits w out:=⟨liftB early _ old.shape.source,trivial⟩
  let priorIdx:Fin (2+A):=finSumFinEquiv (.inl (0:Fin 2));let trimIdx:Fin (2+A):=finSumFinEquiv (.inl (1:Fin 2))
  have keep (s : Fin P) (x : Fin r) (j : Fin K) := (show DescentPackedZip.Fits (C.head s).prior _ (peerExpr ports (key x j) H s) 1 b M out w from
    ⟨DescentPackedChildNeighbor.SIMD.fitted _ _ (reg s x j) (List.finRange P),low_ s x j,(geom priorIdx).1,(geom priorIdx).2,
     by simp [C,view,entries,Book.tables,gate],by simp [C,view,entries,Book.tables,gate]⟩)
  have trim (s : Fin P) (x : Fin r) (j : Fin K) := (show DescentPackedZip.Fits (C.head s).trim _ _ 1 b M out w from
    ⟨hf,readable (keep s x j),(geom trimIdx).1,(geom trimIdx).2,by simp [C,view,entries,Book.tables,gate],by simp [C,view,entries,Book.tables,gate]⟩)
  refine ⟨init.then headers,⟨mounted,fun x j=>reads _ _ (old.routeRoom x j) (old.routeFit x j) (old.routeRead x j),
    fun x j=>reads _ _ (old.keyRoom x j) (old.keyFit x j) (old.keyRead x j),fun x j=>access _ (old.routeRoom x j) (old.routeFit x j),
    fun x j=>access _ (old.keyRoom x j) (old.keyFit x j),source_column hub out hf.1 end_ hubs old.shape.srcRoom (reads _ _ old.shape.srcRoom old.shape.source old.hubsRead),
    reg,queries,keep,trim,?_,?_,?_,?_⟩,intact,cheap_seq cost cheap⟩
  · intro s
    exact fixedTag (.inl 0) ⟨1,b,b,keepRaw⟩ (by simp [gate])
  · intro s
    exact fixedTag (.inl 1) ⟨1,b,Packed.bits low,trimmed k gain slots raw low⟩ (by simp [gate])
  · intro j
    let t : Fin (2+A) := finSumFinEquiv (Sum.inr j)
    let z : Fin (P*r) × Fin K := finProdFinEquiv.symm j
    let part : Fin P × Fin r := finProdFinEquiv.symm z.1
    refine ⟨readable (trim part.1 part.2 z.2),(geom t).1,(geom t).2,?_,?_⟩ <;> simp [C,view,entries,gate,Book.tables]
  · intro j
    exact fixedTag (.inr j) ⟨Packed.bits low*A,Packed.bits low,Packed.bits low*A,Gather.setField j⟩ rfl

end
end Hierarchy.DescentScalarVenueMask.Receiver

end OAI
