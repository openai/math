import OAI.Hierarchy.DescentStageVenueBookLayout
import OAI.Hierarchy.DescentStageVenueDate
import OAI.Hierarchy.DescentStageVenueTariff

namespace OAI
/-! # One public successor input program for arbitrary incoming packed widths -/
open ThreeFlat.RAM.PhysicalProcedure
namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentCompiler DescentPackedColony DescentSIMDLookup DescentPackedZip
open DescentPacking.PackedMatch.Local.Stage DescentActorRaster DescentColonies
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentStaticWordColumn (names names_seq)
open scoped Classical Fin.CommRing
noncomputable section

namespace Date
variable (d:Date) (B:Sources)
section
local notation "r" => 2^d.k
local notation "p" => 2*d.cap
local notation "H" => d.hosts
local notation "G" => d.groups
local notation "M" => d.lanes

def signedPage (i:Fin (r*p)) :=
  let z:Fin r×Fin p:=finProdFinEquiv.symm i
  B.signed z.1.val z.2.val

def transported (base:ℕ):Sources where
  roster:=B.roster
  hub:=B.hub
  signed x j:=DescentVenueSlabs.page d.signedShape base (x*p+j)
  paid x:=DescentVenueSlabs.page d.paidShape (d.firstEnd base) (if x<r then x else 0)
  alive x:=DescentVenueSlabs.page d.aliveShape (d.secondEnd base) x

def operands (base:ℕ):=args (d.transported B base) (d.thirdEnd base) d.k H G M d.degree
def program (base w:ℕ) :=
  (((DescentVenueSlabs.program d.signedShape (d.signedPage B) base w).seq
    (DescentVenueSlabs.program d.paidShape (fun i=>B.paid i.val) (d.firstEnd base) w)).seq
    (DescentVenueSlabs.program d.aliveShape (fun i=>B.alive i.val) (d.secondEnd base) w)).seq
    (StageVenueTail.program (d.transported B base) (d.thirdEnd base) d.k H G M d.degree w)
def ticks (base:ℕ) :=
  ((DescentVenueSlabs.ticks d.signedShape (d.signedPage B) base+
    DescentVenueSlabs.ticks d.paidShape (fun i=>B.paid i.val) (d.firstEnd base))+
    DescentVenueSlabs.ticks d.aliveShape (fun i=>B.alive i.val) (d.secondEnd base))+
    StageVenueTail.ticks (d.transported B base) (d.thirdEnd base) d.k H G M d.degree

def tariff := DescentVenueSlabs.tariff d.signedShape+DescentVenueSlabs.tariff d.paidShape+
    DescentVenueSlabs.tariff d.aliveShape+StageVenueTail.tariff d.k H G M d.degree
theorem price (base w:ℕ) (a:0<d.aliveLanes) (c:0<d.signedLanes) (f:0<d.paidLanes) (n:0<M) :
    d.ticks B base+7*names (d.program B base w)≤d.tariff :=by
  have s₀:=DescentVenueSlabs.price d.signedShape (d.signedPage B) base w c n
  have s₁:=DescentVenueSlabs.price d.paidShape (fun i=>B.paid i.val) (d.firstEnd base) w f n
  have s₂:=DescentVenueSlabs.price d.aliveShape (fun i=>B.alive i.val) (d.secondEnd base) w a n
  have s₃:=StageVenueTail.price (d.transported B base) (d.thirdEnd base) d.k H G M d.degree w
  simp only [program,ticks,tariff,names_seq];omega

theorem translates (base:ℕ):d.endAddress base=base+d.endAddress 0 :=by
  simp only [endAddress,thirdEnd,secondEnd,firstEnd,StageVenueTail.endAddress,StageVenueTail.area,Venue.outBase,
    DescentPackedColumnSum.finish,DescentScalarHaloPortROM.stop,DescentVenueSlabs.endAddress,Overlap.endAddress,
    Overlap.dest,Overlap.dictBase,DescentVenueSlabs.work,Nat.zero_add,Nat.add_assoc]

private theorem step (s : DescentVenueSlabs.Shape) (lo : ℕ) : lo≤DescentVenueSlabs.endAddress s lo :=by
  rw [DescentVenueSlabs.translates];omega

theorem order (base:ℕ):base≤d.firstEnd base ∧ d.firstEnd base≤d.secondEnd base ∧
    d.secondEnd base≤d.thirdEnd base ∧ d.thirdEnd base≤d.endAddress base :=
  ⟨step ..,step ..,step ..,by rw [endAddress,StageVenueTail.translates];omega⟩

structure Space (base w:ℕ):Prop where
  rank : B.roster.Fits w base
  rankSize : H*d.degree≤B.roster.size
  hub : B.hub.Fits w base
  hubSize : H≤B.hub.size
  signed : ∀(x : Fin r)(j:Fin p),(B.signed x.val j.val).Fits w base ∧
    H*chunks G d.signedLanes≤(B.signed x.val j.val).size
  paid : ∀(x:Fin r),(B.paid x.val).Fits w base ∧ H*chunks G d.paidLanes≤(B.paid x.val).size
  alive : ∀(x:Fin r),(B.alive x.val).Fits w base ∧ H*chunks G d.aliveLanes≤(B.alive x.val).size
  roof : d.endAddress base<2^w

end

private theorem high {u v w : ℕ} {T:Bank} (bounds:T.Fits w u) (uv:u≤v) : T.Fits w v:=
  ⟨bounds.1,bounds.2.1,bounds.2.2.trans uv⟩

private def signedCast {a b : ℕ} (same:a=b) (x:Cell a):Cell b:=
  Fin.cast (congrArg (fun n : ℕ=>2^n) same) x

private theorem data_cast {a b H G M : ℕ} (same:a=b)(x:Fin H→Fin G→Cell a)(r:Row H G M):
    (data (fun h g=>signedCast same (x h g)) r).val=(data x r).val:=by
  subst b;rfl

private theorem reads_cast {a b H G M w : ℕ} (same:a=b)(x:Fin H→Fin G→Cell a)(T:Bank)(m:Memory w):
    Reads T (fun h g=>signedCast same (x h g)) M m ↔ Reads T x M m:=by
  subst b;rfl

private theorem carry {u G M a H w : ℕ} {T:Bank} {x:Fin H→Fin G→Cell a} {old new_:Memory w}
    (fit:T.Fits w u) (size:H*chunks G M≤T.size) (frame:∀z,z<u→new_ z=old z)
    (source:Reads T x M old):Reads T x M new_:=by
  intro j;exact (frame _ ((Nat.add_lt_add_left ((row H G M j).isLt.trans_le size) _).trans_le fit.2.2)).trans (source j)

variable {F P:Type} [Field F] {D:ℕ} {bits:P→ℕ} {W:MarkedWorld F D P bits} {gadget:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {age z wire hist w:ℕ}
  (r₀:Reached W gadget q ε S d.k age z d.degree wire hist) (wide:Fintype.card r₀.V≤d.hosts)
local notation "placedStage" => r₀.placement
local notation "placedHost" => r₀.vertex.trans (Fin.castLEEmb wide)
local notation "oldG" => S.groupCount age

theorem successor (base:ℕ) (m:Memory w) (trueG:oldG=d.groups) (trueCap:(placedStage).cap=d.cap)
    (a:0<d.aliveLanes) (c:0<d.signedLanes) (f:0<d.paidLanes)
    (rs:Fin d.hosts→Fin d.degree→Option (Fin d.hosts)) (space:d.Space B base w)
    (roster:∀(h : Fin d.hosts) (j : Fin d.degree),m (B.roster.base+(h.val*d.degree+j.val))=(DescentPackedColony.target (rs h j):Word w))
    (hub:∀h : Fin d.hosts,m (B.hub.base+h.val)=((Census.hub (placedStage) placedHost h).val:Word w))
    (alive:∀x:DescentColonies.Block d.k,Reads (B.alive x.val) (Venue.actual (placedStage) (Function.Embedding.refl _) placedHost x) d.aliveLanes m)
    (funded:∀x:DescentColonies.Block d.k,Reads (B.paid x.val) (fun h g=>Census.count (placedStage) (Equiv.refl _) placedHost d.paidBits h g x) d.paidLanes m)
    (cables:∀(x:DescentColonies.Block d.k)(j:Fin (2*(placedStage).cap)),Reads (B.signed x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (Prepare.signed (placedStage) (r₀.order.trans Fin.valEmbedding)
        S r₀.valid (Function.Embedding.refl _) placedHost x j h g)) d.signedLanes m) :
    ∃out,(d.program B base w).Exec m out (d.ticks B base) ∧
      stageVenue r₀ wide (d.operands B base) d.lanes d.paidBits (d.endAddress base) rs out ∧
      (∀j,j<base ∨ d.endAddress base≤j → out j=m j) ∧ CheapCode (d.program B base w):=by
  cases d with
  | mk k H G deg cap bitsD a₀ s₀ f₀ lanes =>
    dsimp only at *
    subst G
    change Reached W gadget q ε S k age z deg wire hist at r₀
    change r₀.placement.cap = cap at trueCap
    subst cap
    let d:Date:=⟨k,H,S.groupCount age,deg,(r₀.placement).cap,bitsD,a₀,s₀,f₀,lanes⟩
    let A:=r₀.placement
    let host:=r₀.vertex.trans (Fin.castLEEmb wide)
    let idg:=Function.Embedding.refl (Fin (S.groupCount age))
    let widthEq:DescentSignedCableCodec.width A.degree A.cap=DescentSignedCableCodec.width deg A.cap:=
      congrArg (fun n=>DescentSignedCableCodec.width n A.cap) r₀.branch
    let sign := fun (q:Fin (2^k*(2*A.cap))) (h:Fin H) (g:Fin (S.groupCount age))=>
      let j:Fin (2^k)×Fin (2*A.cap):=finProdFinEquiv.symm q
      signedCast widthEq (DescentSignedCableCodec.encode (Prepare.signed A (r₀.order.trans Fin.valEmbedding) S r₀.valid idg host j.1 j.2 h g))
    obtain ⟨o₀,o₁,o₂,o₃⟩:=d.order base
    have limit:=space.roof
    have signed_:=DescentVenueSlabs.run d.signedShape (d.signedPage B) base m sign
      (fun j=>(space.signed _ _).1) (fun j=>(space.signed _ _).2) (fun j=>(reads_cast widthEq _ _ _).mpr (cables _ _)) c
      ((o₁.trans (o₂.trans o₃)).trans_lt limit)
    obtain ⟨run₀,read₀,fit₀,hold₀,cheap₀⟩:=signed_
    let mid₀:=DescentVenueSlabs.image d.signedShape (d.signedPage B) base m
    have charges:=DescentVenueSlabs.run d.paidShape (fun j=>B.paid j.val) (d.firstEnd base) mid₀
      (fun x h g=>Census.count A (Equiv.refl _) host bitsD h g x) (fun x=>high (space.paid x).1 o₀)
      (fun x=>(space.paid x).2) (fun x=>carry (space.paid x).1 (space.paid x).2 (fun j lt=>hold₀ j (.inl lt)) (funded x))
      f ((o₂.trans o₃).trans_lt limit)
    obtain ⟨run₁,read₁,fit₁,hold₁,cheap₁⟩:=charges
    let mid₁:=DescentVenueSlabs.image d.paidShape (fun j=>B.paid j.val) (d.firstEnd base) mid₀
    have firstKeep (j:ℕ)(lt:j<base):mid₁ j=m j:=(hold₁ j (.inl (lt.trans_le o₀))).trans (hold₀ j (.inl lt))
    have lives:=DescentVenueSlabs.run d.aliveShape (fun x=>B.alive x.val) (d.secondEnd base) mid₁
      (Venue.actual A idg host) (fun x=>high (space.alive x).1 (o₀.trans o₁)) (fun x=>(space.alive x).2)
      (fun x=>carry (space.alive x).1 (space.alive x).2 firstKeep (alive x)) a (o₃.trans_lt limit)
    obtain ⟨run₂,read₂,fit₂,hold₂,cheap₂⟩:=lives
    let prior:=DescentVenueSlabs.image d.aliveShape (fun x=>B.alive x.val) (d.secondEnd base) mid₁
    have allKeep (j:ℕ)(lt:j<base):prior j=m j:=(hold₂ j (.inl (lt.trans_le (o₀.trans o₁)))).trans (firstKeep j lt)
    have signedIndex (x : Fin (2^k)) (j : Fin (2*A.cap)) :
        (finProdFinEquiv (x,j)).val = x.val*(2*A.cap)+j.val := by
      simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have signedFit (x:Fin (2^k))(j:Fin (2*A.cap)):
        let e:=DescentVenueSlabs.page d.signedShape base (x.val*(2*A.cap)+j.val)
        e.Fits w (d.firstEnd base) ∧ H*chunks (S.groupCount age) lanes≤e.size:=by
      dsimp only
      rw [←signedIndex x j]
      exact fit₀ (finProdFinEquiv (x,j))
    have fees (x:Fin (2^k)) : (d.transported B base).paid x.val=DescentVenueSlabs.page d.paidShape (d.firstEnd base) x.val :=by
      change DescentVenueSlabs.page _ _ (if x.val < 2^k then x.val else 0) = _
      rw [ite_eq_left x.isLt]
    have bound:Room (d.transported B base) (d.thirdEnd base) k H (S.groupCount age) lanes deg A.cap w:=by
      refine ⟨high space.rank (o₀.trans (o₁.trans o₂)),space.rankSize,high space.hub (o₀.trans (o₁.trans o₂)),space.hubSize,
        fun x=>(fit₂ x).1,fun x=>(fit₂ x).2,?_,?_,fun x j=>high (signedFit x j).1 (o₁.trans o₂),
        fun x j=>(signedFit x j).2,limit⟩
      · intro x
        let idx:Fin (2^k):=⟨if x<2^k then x else 0,by split <;> first | assumption | positivity⟩
        exact high (fit₁ idx).1 o₂
      · intro x;rw [fees x];exact (fit₁ x).2
    obtain ⟨last,installed,frame,cheap⟩:=issued r₀ wide (d.transported B base) (d.thirdEnd base) prior rs bound
      (fun h j=>by
        have small:h.val*deg+j.val<H*deg:=by simpa [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (h,j)).isLt
        exact (allKeep _ ((Nat.add_lt_add_left (small.trans_le space.rankSize) _).trans_le space.rank.2.2)).trans (roster h j))
      (fun h=>(allKeep _ ((Nat.add_lt_add_left (h.isLt.trans_le space.hubSize) _).trans_le space.hub.2.2)).trans (hub h))
      read₂ (fun x=>by
        rw [fees x]
        exact carry (fit₁ x).1 (fit₁ x).2 (fun j lt=>hold₂ j (.inl lt)) (read₁ x))
      (fun x j=>by
        have refs:=read₀ (finProdFinEquiv (x,j))
        apply carry (high (signedFit x j).1 o₁) (signedFit x j).2 (fun at_ lt=>hold₂ at_ (.inl lt))
        apply carry (signedFit x j).1 (signedFit x j).2 (fun at_ lt=>hold₁ at_ (.inl lt))
        let raw := fun h g => DescentSignedCableCodec.encode
          (Prepare.signed A (r₀.order.trans Fin.valEmbedding) S r₀.valid idg host x j h g)
        change Reads (DescentVenueSlabs.page d.signedShape base (x.val*(2*A.cap)+j.val)) raw lanes mid₀
        rw [←signedIndex x j]
        apply (reads_cast widthEq raw _ mid₀).mp
        simpa only [sign,Equiv.symm_apply_apply,raw,mid₀,signedShape,d,A] using refs)
    refine ⟨_,by
      intro P R K machine pc regs pubs exit rom advice cfg memory enter same
      exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then run₀ run₁) run₂) last machine pc regs pubs exit rom advice cfg memory enter same,installed,?_,cheap_seq (cheap_seq (cheap_seq cheap₀ cheap₁) cheap₂) cheap⟩
    rintro j (low|late)
    · exact (frame j (.inl (low.trans_le (o₀.trans (o₁.trans o₂))))).trans (allKeep j low)
    · exact (frame j (.inr late)).trans ((hold₂ j (.inr (o₃.trans late))).trans
        ((hold₁ j (.inr (o₂.trans (o₃.trans late)))).trans (hold₀ j (.inr (o₁.trans (o₂.trans (o₃.trans late)))))))

end Date
end
end Hierarchy.DescentSixParty.StageVenueTail

end OAI
