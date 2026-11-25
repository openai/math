import OAI.Hierarchy.DescentVenueSlabPhase
import OAI.Hierarchy.DescentStageVenueChange
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # The identical fixed successor clock on arbitrary protocol memories -/
open ThreeFlat.RAM.PhysicalProcedure
namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentSIMDLookup DescentActorRaster DescentPackedZip DescentColonies Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM

theorem cheap (B:Sources) (base k H G M D w:ℕ):CheapCode (program B base k H G M D w):=by
  apply cheap_seq
  · exact DescentPackedColumnSum.program_cheap w base (Venue.outBase base k M) 1 M (1*2^k) H G
      (fun _ : Fin (2^k)=>1) Venue.place (input B k)
  · exact @DescentStaticWordColumn.cheap _ _ _ _

theorem any {w : ℕ} (B:Sources) (base k H G M D cap:ℕ) (m:Memory w) (fit:Room B base k H G M D cap w):
    (program B base k H G M D w).Exec m (image B base k H G M D m) (ticks B base k H G M D) ∧
    ∀j,j<base ∨ endAddress base k H G M D≤j→image B base k H G M D m j=m j:=by
  let next:=area base k H G M
  let ptr:=Venue.outBase base k M
  let length_:=DescentScalarHaloPortROM.length H G M D
  have before:base≤ptr:=Nat.le_add_right ..
  have after:ptr+H*chunks G M≤next:=Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  have slot:next+length_≤endAddress base k H G M D:=Nat.le_add_right ..
  have pspace:ptr+H*chunks G M<2^w:=after.trans_lt ((Nat.le_add_right ..).trans_lt (slot.trans_lt fit.room))
  let mid:=Venue.after base k H G M (input B k) m
  have init : (Venue.program w base k H G M (input B k)).Exec m mid (Venue.ticks base k H G M (input B k)) :=
    DescentPackedColumnSum.any base ptr 1 M (1*2^k) H G (fun _ : Fin (2^k)=>1) Venue.place
    (input B k) m (fun _=>le_rfl) (fun x=>⟨fit.alive x,True.intro⟩) le_rfl pspace
  obtain ⟨last,_,keep,_⟩:=DescentScalarHaloPortROM.mount H G M D next B.roster mid (slot.trans_lt fit.room)
  let rom:=DescentStaticWordColumn.image base (DescentPackedColumnSum.literals 1 M (1*2^k) (fun _ : Fin (2^k)=>1) Venue.place) m ((2^k)*2^(1*M))
  let op:=DescentPackedColumnSum.reads base 1 M (fun _ : Fin (2^k)=>1) (input B k)
  refine ⟨by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then init last machine pc regs pubs exit rom advice cfg memory enter same,?_⟩
  rintro j (lo|hi)
  · have t₀:j<ptr:=lo.trans_le before
    exact (keep j (.inl (t₀.trans_le ((Nat.le_add_right ..).trans after)))).trans
      ((ProtocolRAMGeneratedWrite.frame_image ptr _ op rom j (.inl t₀)).trans
        (DescentStaticWordColumn.frame _ _ _ _ j (.inl lo)))
  · have past₁:ptr+H*chunks G M≤j:=after.trans ((Nat.le_add_right ..).trans (slot.trans hi))
    have past₀:base+2^k*2^(1*M)≤j:=(Nat.le_add_right ptr _).trans past₁
    exact (keep j (.inr (slot.trans hi))).trans
      ((ProtocolRAMGeneratedWrite.frame_image ptr _ op rom j (.inr past₁)).trans
        (DescentStaticWordColumn.frame _ _ _ _ j (.inr past₀)))

namespace Date
open DescentCompiler DescentPackedColony DescentPacking.PackedMatch.Local.Stage Chronology
open scoped Fin.CommRing
noncomputable section
variable (d:Date) (B:Sources)
def image {w : ℕ} (base:ℕ) (m:Memory w) :=
  let s:=DescentVenueSlabs.image d.signedShape (d.signedPage B) base m
  let p:=DescentVenueSlabs.image d.paidShape (fun x=>B.paid x.val) (d.firstEnd base) s
  let a:=DescentVenueSlabs.image d.aliveShape (fun x=>B.alive x.val) (d.secondEnd base) p
  StageVenueTail.image (d.transported B base) (d.thirdEnd base) d.k d.hosts d.groups d.lanes d.degree a

def phase (base w:ℕ):NativePhase w where
  program:=d.program B base w
  ticks:=d.ticks B base
  image:=d.image B base
  cheap:=cheap_seq (cheap_seq (cheap_seq (DescentVenueSlabs.cheap d.signedShape (d.signedPage B) base w)
      (DescentVenueSlabs.cheap d.paidShape (fun x=>B.paid x.val) (d.firstEnd base) w))
    (DescentVenueSlabs.cheap d.aliveShape (fun x=>B.alive x.val) (d.secondEnd base) w))
    (StageVenueTail.cheap (d.transported B base) (d.thirdEnd base) d.k d.hosts d.groups d.lanes d.degree w)

theorem any {w : ℕ} (base:ℕ) (m:Memory w) (fit:d.Space B base w) :
    (d.phase B base w).Runs m ∧
    ∀j,j<base ∨ d.endAddress base≤j→d.image B base m j=m j:=by
  obtain ⟨o₀,o₁,o₂,o₃⟩:=d.order base
  have space:=fit.roof
  have bankHigh {T:Bank} {u v:ℕ}(f:T.Fits w u)(uv:u≤v):T.Fits w v:=⟨f.1,f.2.1,f.2.2.trans uv⟩
  let s:=DescentVenueSlabs.image d.signedShape (d.signedPage B) base m
  let p:=DescentVenueSlabs.image d.paidShape (fun x=>B.paid x.val) (d.firstEnd base) s
  let a:=DescentVenueSlabs.image d.aliveShape (fun x=>B.alive x.val) (d.secondEnd base) p
  have rs:=(o₁.trans (o₂.trans o₃)).trans_lt space
  have rp:=(o₂.trans o₃).trans_lt space
  have ra:=o₃.trans_lt space
  obtain ⟨issuedS,frameS⟩:=DescentVenueSlabs.any d.signedShape (d.signedPage B) base m (fun i=>(fit.signed _ _).1) rs
  obtain ⟨issuedP,frameP⟩:=DescentVenueSlabs.any d.paidShape (fun x=>B.paid x.val) (d.firstEnd base) s
    (fun i=>bankHigh (fit.paid i).1 o₀) rp
  obtain ⟨issuedA,frameA⟩:=DescentVenueSlabs.any d.aliveShape (fun x=>B.alive x.val) (d.secondEnd base) p
    (fun i=>bankHigh (fit.alive i).1 (o₀.trans o₁)) ra
  have last:Room (d.transported B base) (d.thirdEnd base) d.k d.hosts d.groups d.lanes d.degree d.cap w:=by
    have signedIndex (x : DescentColonies.Block d.k) (j : Fin (2*d.cap)) :
        (finProdFinEquiv (x,j)).val = x.val*(2*d.cap)+j.val := by
      simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have signedFit (x : DescentColonies.Block d.k) (j : Fin (2*d.cap)) :
        let page:=DescentVenueSlabs.page d.signedShape base (x.val*(2*d.cap)+j.val)
        page.Fits w (d.firstEnd base) ∧ d.hosts*chunks d.groups d.lanes≤page.size:=by
      dsimp only
      rw [←signedIndex x j]
      exact DescentVenueSlabs.output_room d.signedShape base rs (finProdFinEquiv (x,j))
    have paidFit:=DescentVenueSlabs.output_room d.paidShape (d.firstEnd base) rp
    have aliveFit:=DescentVenueSlabs.output_room d.aliveShape (d.secondEnd base) ra
    refine ⟨bankHigh fit.rank (o₀.trans (o₁.trans o₂)),fit.rankSize,bankHigh fit.hub (o₀.trans (o₁.trans o₂)),
      fit.hubSize,fun x=>(aliveFit x).1,fun x=>(aliveFit x).2,?_,?_,?_,?_,fit.roof⟩
    · intro x
      let i:DescentColonies.Block d.k:=⟨if x<2^d.k then x else 0,by split <;> first | assumption | positivity⟩
      exact bankHigh (paidFit i).1 o₂
    · intro x
      change _ ≤ (DescentVenueSlabs.page _ _ (if x.val < 2^d.k then x.val else 0)).size
      rw [ite_eq_left x.isLt]
      exact (paidFit x).2
    · intro x j
      exact bankHigh (signedFit x j).1 (o₁.trans o₂)
    · intro x j
      exact (signedFit x j).2
  obtain ⟨ran,frame⟩:=StageVenueTail.any (d.transported B base) (d.thirdEnd base) d.k d.hosts d.groups d.lanes d.degree d.cap a last
  refine ⟨by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then issuedS issuedP) issuedA) ran machine pc regs pubs exit rom advice cfg memory enter same,?_⟩
  rintro j (lo|hi)
  · exact (frame j (.inl (lo.trans_le (o₀.trans (o₁.trans o₂))))).trans
      ((frameA j (.inl (lo.trans_le (o₀.trans o₁)))).trans ((frameP j (.inl (lo.trans_le o₀))).trans (frameS j (.inl lo))))
  · exact (frame j (.inr hi)).trans ((frameA j (.inr (o₃.trans hi))).trans
      ((frameP j (.inr (o₂.trans (o₃.trans hi)))).trans (frameS j (.inr (o₁.trans (o₂.trans (o₃.trans hi)))))))

variable {F P:Type} [Field F] {D:ℕ} {bits:P→ℕ} {W:MarkedWorld F D P bits} {gadget:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {age z wire hist w:ℕ}
  (r₀:Reached W gadget q ε S d.k age z d.degree wire hist) (wide:Fintype.card r₀.V≤d.hosts)
local notation "placedStage" => r₀.placement
local notation "placedHost" => r₀.vertex.trans (Fin.castLEEmb wide)
local notation "oldG" => S.groupCount age

theorem phase_source (base:ℕ) (m:Memory w) (trueG:oldG=d.groups) (trueCap:(placedStage).cap=d.cap)
    (a:0<d.aliveLanes) (c:0<d.signedLanes) (f:0<d.paidLanes)
    (rs:Fin d.hosts→Fin d.degree→Option (Fin d.hosts)) (space:d.Space B base w)
    (roster:∀(h : Fin d.hosts) (j : Fin d.degree),m (B.roster.base+(h.val*d.degree+j.val))=(DescentPackedColony.target (rs h j):Word w))
    (hub:∀h : Fin d.hosts,m (B.hub.base+h.val)=((Census.hub (placedStage) placedHost h).val:Word w))
    (alive:∀x:DescentColonies.Block d.k,Reads (B.alive x.val) (Venue.actual (placedStage) (Function.Embedding.refl _) placedHost x) d.aliveLanes m)
    (funded:∀x:DescentColonies.Block d.k,Reads (B.paid x.val) (fun h g=>Census.count (placedStage) (Equiv.refl _) placedHost d.paidBits h g x) d.paidLanes m)
    (cables:∀(x:DescentColonies.Block d.k)(j:Fin (2*(placedStage).cap)),Reads (B.signed x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (Prepare.signed (placedStage) (r₀.order.trans Fin.valEmbedding)
        S r₀.valid (Function.Embedding.refl _) placedHost x j h g)) d.signedLanes m) :
    stageVenue r₀ wide (d.operands B base) d.lanes d.paidBits (d.endAddress base) rs (d.image B base m):=by
  obtain ⟨out,physical,receipt,_⟩:=d.successor B r₀ wide base m trueG trueCap a c f rs space roster hub alive funded cables
  have fixed:=d.any B base m space
  have same:=ProtocolRAM.exec_unique (d.program B base w) m out (d.image B base m) physical fixed.1
  exact same ▸ receipt

end
end Date
end Hierarchy.DescentSixParty.StageVenueTail

end OAI
