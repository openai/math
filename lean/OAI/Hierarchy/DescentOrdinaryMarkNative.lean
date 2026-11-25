import OAI.Hierarchy.DescentOrdinaryMarkPhase
import OAI.Hierarchy.DescentResetStemProjectExprTariff
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # The original mark publisher as a paid chronological RAM phase -/
namespace Hierarchy.DescentOrdinaryMarkProject
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedCableNames
open DescentOrdinarySignedMeta DescentSixParty.Chronology DescentDyadicSpan
open DescentPacking.PackedMatch.Local
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentStaticWordColumn (names names_seq)
open scoped Classical Fin.CommRing
noncomputable section
variable {P O N H G X D cap M A w : ℕ}

theorem extent (base P O N H G X D cap A M : ℕ) :
    endpoint base P O N H G X D cap A M=base+endpoint 0 P O N H G X D cap A M := by
  simp only [endpoint,stop,region,MarkGather.stop,Nat.zero_add]
  rw [DescentResetStemProject.extent (base+_),DescentResetStemProject.extent (4*_)]
  omega

theorem pick_fits (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base : ℕ) (j : Fin (P*O))
    (access : ∀o,Accessible ports (prior o) N (G*X) A w base) (room : MarkGather.stop base D cap A<2^w) :
    (pick ports prior fresh base D cap N A j).Fits w (MarkGather.stop base D cap A) := by
  let q:=finProdFinEquiv.symm j
  let mode:=fresh q.2
  let width:=MarkGather.width D cap A
  let pages:=MarkGather.pages D cap A
  let t:=MarkGather.lut base D cap A mode
  let e:=peerExpr ports (prior q.2) N q.1
  have ee : e.Fits w (MarkGather.stop base D cap A) :=
    ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (peer_fits ports _ base (access q.2) q.1)
  have data (i : Fin (2+2)) : (DescentOrdinaryAtomFieldRAM.ROM.bank pages width base i).Fits w (MarkGather.stop base D cap A) :=
    DescentOrdinaryAtomFieldRAM.ROM.bank_room pages width base _ i (MarkGather.page_bits D cap A i).le le_rfl room
  change (t.read e (.lit 0)).Fits w (MarkGather.stop base D cap A)
  exact ⟨data _,trivial,data _,ee⟩

theorem cut_le (base P O N G X D cap A M : ℕ) :
    MarkGather.stop base D cap A≤region base P O N G X D cap A M := by
  obtain ⟨r₁,r₂,r₃,r₄,r₅⟩:=DescentResetStemProject.regions (N:=P*O) (MarkGather.stop base D cap A) N G X 1 A M
  exact (Nat.le_add_right ..).trans (r₁.trans (r₂.trans ((Nat.le_add_right ..).trans (r₃.trans (r₄.trans ((Nat.le_add_right ..).trans r₅))))))

structure Safe (ports : Ports P) (prior : Fin O→Bank) (base N H G X D cap A M w : ℕ) : Prop where
  lanes : 0<M
  blocks : 0<X
  access : ∀o,Accessible ports (prior o) N (G*X) A w base
  room : endpoint base P O N H G X D cap A M<2^w

set_option maxHeartbeats 550000 in
theorem any (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base pitch : ℕ)
    (good : Safe ports prior base N H G X D cap A M w) (m : Memory w) :
    let dst:=memory ports prior fresh base N H G X D cap A M pitch m
    (program ports prior fresh base N H G X D cap A M pitch w).Exec m dst (ticks ports prior fresh base N H G X D cap A M) ∧
    (∀u,u<base ∨ endpoint base P O N H G X D cap A M≤u→dst u=m u) ∧
    CheapCode (program ports prior fresh base N H G X D cap A M pitch w) := by
  intro dst
  let pg:=MarkGather.pages D cap A
  let aw:=MarkGather.width D cap A
  let cut:=MarkGather.stop base D cap A
  let mid:=region base P O N G X D cap A M
  let roof:=endpoint base P O N H G X D cap A M
  let first:=DescentOrdinaryAtomFieldRAM.ROM.after pg aw base m
  let src:=pick ports prior fresh base D cap N A
  let second:=DescentResetStemProjectExpr.image cut N G X 1 A M src first
  have ordered : cut≤ mid :=cut_le base P O N G X D cap A M
  have post : mid≤roof:=Nat.le_add_right ..
  have sr : cut<2^w:=(ordered.trans post).trans_lt good.room
  have startOf : base≤cut :=Nat.le_add_right ..
  let mountProgram := DescentOrdinaryAtomFieldRAM.ROM.mount pg aw w base
  let projectProgram := DescentResetStemProjectExpr.program cut N G X 1 A M src w
  let wordsProgram := DescentStaticWordColumn.program w mid (words N H G M pitch) (rows H G M)
  have lead : mountProgram.Exec m first (4+10*(4*2^aw)) := DescentStaticWordColumn.mount base (4*2^aw) (DescentOrdinaryAtomFieldRAM.ROM.contents pg aw) m sr
  have next:=DescentResetStemProjectExpr.any cut N G X 1 A M src first good.lanes good.blocks (fun j=>pick_fits ports prior fresh base j good.access sr) (post.trans_lt good.room)
  have span : mid+rows H G M≤roof :=Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  have last : wordsProgram.Exec second dst (4+10*rows H G M) := DescentStaticWordColumn.mount mid (rows H G M) (words N H G M pitch) second (span.trans_lt good.room)
  refine ⟨Procedure.Exec.then (A:=mountProgram) (B:=projectProgram.seq wordsProgram) lead
    (Procedure.Exec.then (A:=projectProgram) (B:=wordsProgram) next.1 last),?_,?_⟩
  · intro u away
    rcases away with lo|hi
    · exact (DescentStaticWordColumn.frame _ _ _ _ u (.inl (lo.trans_le (startOf.trans ordered)))).trans
        ((next.2.1 u (.inl (lo.trans_le startOf))).trans (DescentOrdinaryAtomFieldRAM.ROM.frame pg aw base m u (.inl lo)))
    · exact (DescentStaticWordColumn.frame _ _ _ _ u (.inr (span.trans hi))).trans
        ((next.2.1 u (.inr (post.trans hi))).trans (DescentOrdinaryAtomFieldRAM.ROM.frame pg aw base m u (.inr ((ordered.trans post).trans hi))))
  · exact @cheap_seq w mountProgram (projectProgram.seq wordsProgram)
      (DescentOrdinaryAtomFieldRAM.ROM.cheap pg aw w base)
      (@cheap_seq w projectProgram wordsProgram next.2.2
        (@DescentStaticWordColumn.cheap w mid (words N H G M pitch) (rows H G M)))

def native (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base pitch : ℕ)
    (good : Safe ports prior base N H G X D cap A M w) : NativePhase w where
  program:=program ports prior fresh base N H G X D cap A M pitch w
  ticks:=ticks ports prior fresh base N H G X D cap A M
  image:=memory ports prior fresh base N H G X D cap A M pitch
  cheap:=(any ports prior fresh base pitch good (fun _=>0)).2.2

def bill (P O N H G X D cap A M : ℕ) :=
  let sites:=rows H G M
  let header:=4*2^MarkGather.width D cap A
  let n:=P*O
  (4+10*header)+7*(15*(header+1))+
    (4096*DescentResetStemProject.volume n N G X 1 A M+
      (4+n*(4+N*chunks (G*X) A*(2*57+4)))+7*(15+n*(11+4*57)))+
    ((4+10*sites)+7*(15*(sites+1)))

theorem native_bill (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base pitch : ℕ)
    (good : Safe ports prior base N H G X D cap A M w) (old : 0<A) :
    let p:=native ports prior fresh base pitch good
    p.ticks+7*names p.program≤bill P O N H G X D cap A M := by
  let src:=pick ports prior fresh base D cap N A
  have work (j : Fin (P*O)) : (src j).work≤57 := (MarkGather.work base D cap A N _ ports _ _).le
  have paid:=DescentResetStemProjectExpr.tariff (MarkGather.stop base D cap A) N G X 1 A M w src 57 work old good.blocks good.lanes
  dsimp only [src] at paid
  dsimp only [native,program,ticks,bill]
  rw [names_seq,names_seq,DescentStaticWordColumn.names_mount]
  change _+7*(names (DescentStaticWordColumn.program w base _ (4*2^MarkGather.width D cap A))+_)≤_
  rw [DescentStaticWordColumn.names_mount]
  omega

end
end Hierarchy.DescentOrdinaryMarkProject

end OAI
