import OAI.Hierarchy.DescentOrdinarySignedDate
import OAI.Hierarchy.DescentOrdinaryDonorSources
import OAI.Hierarchy.DescentOrdinaryRankSweep

namespace OAI
/-! Final ordinary signed publication from measured donor material and its
five dynamic geometric rank sheets. The common peer formatter is mounted
once before the public ranked and signed-cell passes. -/
namespace Hierarchy.DescentOrdinarySignedNative
open DescentSixParty DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM DescentOrdinarySignedDate
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical
noncomputable section
variable {F Pin U J E X T V:Type} [Field F] [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype E] [Fintype X] [Fintype T]
  {d k i D Q O K L b M hosts groups blocks oldH w:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ}
local notation "c" => breadth D*O
local notation "P" => breadth D

structure Donor where
  material:Fin 6→Expr
  ranks:Fin 5→Expr

def Donor.Fits (d:Donor) (w base:ℕ):Prop:=(∀i,(d.material i).Fits w base) ∧ (∀i,(d.ranks i).Fits w base)

def Donor.Measured (d:Donor) (R:Fin oldH→Fin D→Option (Fin oldH)) (raw:Fin hosts→Fin groups→Option (Fused.Raw R Q K L b))
    (fit:P*P<2^b) (M:ℕ) (m:Memory w):Prop:=
  (∀i,Source (d.material i) (fun v g=>DescentOrdinaryDonorSources.material R (raw v g) i) M m) ∧
  (∀i,Source (d.ranks i) (fun v g=>DescentOrdinaryDonorSources.geometry R fit (raw v g) i) M m)

structure Inputs (blocks capacity:ℕ) where
  «meta»:Fin blocks→Fin capacity→Expr
  query:Fin blocks→Fin 3→Fin capacity→Donor
  items:Fin blocks→Fin 3→Fin capacity→Fin capacity→Donor

def Inputs.layout (I:Inputs blocks (breadth D*O)) (tab:Tables):Layout blocks (breadth D*O):=
  ⟨I.meta,fun x p j=>let d:=I.query x p j;DescentOrdinaryDonorSources.assemble tab d.material d.ranks,
    fun x p j t=>let d:=I.items x p j t;DescentOrdinaryDonorSources.assemble tab d.material d.ranks⟩

variable (A:GroupStage W G price ε J U k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule)
  (ready:A.StateBounds S i) (names:Stage.Host J U k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u p,R v p=some u→∃z,R u z=some v)
  (Z:Measured C R X T V Q O K A.cap) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K A.cap) f,Machine.fields R (Z.venue h) path (Z.loc x).1 s f<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
  (home:Fin blocks→Fin hosts→Fin groups→Option (Stage.Host J U k)) (I:Inputs blocks (breadth D*O)) (base:ℕ)
local notation "tab" => DescentOrdinaryDonorSources.ROM.table base Q b M
local notation "census" => Incidence.of_measured C R symm Z orders
local notation "qr" => queryRaw C R symm Z shelf small orders home
local notation "ar" => itemRaw C R symm Z shelf small orders home
local notation "src" => DescentOrdinarySignedWindows.header A native S ready names C marked census home
local notation "target" => DescentOrdinarySignedWindows.target A native S ready names home
local notation "next" => DescentOrdinaryDonorSources.ROM.endAddress base b M
local notation "afterROM" => DescentOrdinarySignedParents.ROM.endAddress next D Q K A.cap b M
local notation "end'" => DescentOrdinarySignedAll.endAddress afterROM blocks c A.cap b M hosts groups
local notation "book" => DescentOrdinaryDonorSources.ROM.pages Q b M
local notation "width" => DescentOrdinaryDonorSources.ROM.width b M

theorem issued (m:Memory w) (emit:DescentResetWindowFields.Emission A native C marked)
    (hf:∀x j,(I.meta x j).Fits w base) (qf:∀x p j,(I.query x p j).Fits w base) (af:∀x p j t,(I.items x p j t).Fits w base)
    (capacity:P*P<2^b)
    (queries:∀x p j,(I.query x p j).Measured R (qr x p j) capacity M m)
    (items:∀x p j t,(I.items x p j t).Measured R (ar x p j t) capacity M m)
    (hd:∀x j,Source (I.meta x j) (fun v g=>DescentResetFieldAssembler.raw b (src x j v g)) M m)
    (rawRoom:∀x j h g f,DescentResetFieldAssembler.digits (src x j h g) f<2^b)
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:P*P*Q≤2^b) (tickets:K≤2^b) (space:end'<2^w):
    let p₀:=DescentOrdinaryAtomFieldRAM.ROM.mount book width w base
    let after:=DescentOrdinaryAtomFieldRAM.ROM.after book width base m
    let lay:=I.layout tab
    let done:=Layout.memory lay next D Q K A.cap b M A.degree hosts groups after
    (p₀.seq (Layout.program lay next D Q K A.cap b M A.degree hosts groups w)).Exec m done
      ((4+10*(2*2^width))+Layout.time lay next D Q K A.cap b M A.degree hosts groups) ∧
    (∀x j,Reads (Layout.output («c»:=c) next D Q K A.cap b M x j hosts groups) (fun h g=>DescentSignedCableCodec.encode (target x j h g)) M done) ∧
    (∀u,u<base ∨ end'≤u→done u=m u) ∧ CheapCode (p₀.seq (Layout.program lay next D Q K A.cap b M A.degree hosts groups w)):=by
  intro p₀ after lay done
  have top:next≤end':=by
    have lo:=DescentOrdinarySignedAll.ordered (X:=blocks) (K:=c) (b:=b) (M:=M) (H:=hosts) (gg:=groups) (cap:=A.cap) afterROM
    have a:next≤afterROM:=by unfold DescentOrdinarySignedParents.ROM.endAddress;omega
    exact a.trans (lo.1.trans lo.2)
  obtain ⟨load,static,frame,cheapRom⟩:=DescentOrdinaryDonorSources.ROM.setup base Q b M m (top.trans_lt space)
  have low:base≤next:=Nat.le_add_right ..
  have transport (e:Expr) {s:ℕ} (f:Fin hosts→Fin groups→Cell s) (early:e.Fits w base) (read:Source e f M m):Source e f M after:=
    fun p=>(eval_below e _ m after early (fun u hu=>frame _ (.inl hu))).trans (read p)
  have pg (j:Fin 2): (book j).bits≤width:=by fin_cases j <;> change _*M≤_*M <;> apply Nat.mul_le_mul_right <;> omega
  have page (j:Fin 2):=(DescentOrdinaryAtomFieldRAM.ROM.bank_room book width base next j (pg j) le_rfl (top.trans_lt space))
  have bounds (u v:Expr) (hu:u.Fits w base) (hv:v.Fits w base): DescentPackedZip.Fits tab u v b b M next w:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ low hu,ProtocolRAMGeneratedWrite.fits_mono _ low hv,page 0,page 1,
      by rfl,by rfl⟩
  have observed (z:Donor) (raw:Fin hosts→Fin groups→Option (Fused.Raw R Q K A.cap b))
      (fit:z.Fits w base) (reads:z.Measured R raw capacity M m)
      (correct:∀h g v,raw h g=some v→Gather.select (Gather.reaching R) v.receiver.1 v.path=some v.host):
      (∀i,(DescentOrdinaryDonorSources.assemble tab z.material z.ranks i).Fits w next) ∧
      (∀i,Source (DescentOrdinaryDonorSources.assemble tab z.material z.ranks i) (fun h g=>Fused.columns (raw h g) i) M after):=by
    constructor
    · have g (i:Fin 5):=(ProtocolRAMGeneratedWrite.fits_mono _ low (fit.2 i))
      have e (i:Fin 6):=(ProtocolRAMGeneratedWrite.fits_mono _ low (fit.1 i))
      have pair (i:Fin 5) (j:Fin 6):((tab).read (z.ranks i) (z.material j)).Fits w next:=⟨page 1,e j,page 0,g i⟩
      intro i;fin_cases i <;> first | exact pair _ _ | exact g _ | exact e _
    · apply DescentOrdinaryDonorSources.source R tab z.material z.ranks capacity after next raw correct
      · intro i;exact transport _ _ (fit.1 i) (reads.1 i)
      · intro i;exact transport _ _ (fit.2 i) (reads.2 i)
      · exact fun i j=>bounds _ _ (fit.2 i) (fit.1 j)
      · exact static
  have seenQ (x p j):=observed _ (qr x p j) (qf x p j) (queries x p j)
    (fun h g v read=>DescentOrdinaryDonorSources.corrected_bind R C Z shelf small _ _ _ v read)
  have seenA (x p j t):=observed _ (ar x p j t) (af x p j t) (items x p j t)
    (fun h g v read=>DescentOrdinaryDonorSources.corrected_bind R C Z shelf small _ _ _ v read)
  obtain ⟨run,issued,kept,cheap⟩:=DescentOrdinarySignedDate.issued A native S ready names C marked R symm Z shelf small orders home lay next after emit
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ low (hf x j)) (fun x p j=>(seenQ x p j).1)
    (fun x p j t=>(seenA x p j t).1) (fun x p j=>(seenQ x p j).2) (fun x p j t=>(seenA x p j t).2)
    (fun x j=>transport _ _ (hf x j) (hd x j)) rawRoom digits codes tickets space
  exact ⟨Procedure.Exec.then load run,issued,fun u away=>(kept u (away.imp (·.trans_le low) id)).trans
    (frame u (away.imp id (top.trans ·))),cheap_seq cheapRom cheap⟩

end
end Hierarchy.DescentOrdinarySignedNative

end OAI
