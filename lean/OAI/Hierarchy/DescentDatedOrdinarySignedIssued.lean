import OAI.Hierarchy.DescentDatedOrdinarySignedPhase

namespace OAI
/-! Pointwise join of the immutable donor provenance to the one public
dated procedure. Every published word is taken from exactly its phase
image on the original input, including absent hosts and padded lanes. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty DescentSixParty.Chronology DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin U J E X T V:Type} [Field F] [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype E] [Fintype X] [Fintype T]
  {d k i D Q O K b M H groups blocks oldH w:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ}
variable (A:GroupStage W G price ε J U k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule)
  (ready:A.StateBounds S i) (names:Stage.Host J U k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u p,R v p=some u→∃z,R u z=some v)
  (Z:Measured C R X T V Q O K A.cap) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K A.cap) f,Machine.fields R (Z.venue h) path (Z.loc x).1 s f<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
  (home:Fin blocks→Fin H→Fin groups→Option (Stage.Host J U k))
local notation "e₀" => (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent)
local notation "census" => Incidence.of_measured C R symm Z orders
local notation "qr" => queryRaw C R symm Z shelf small orders home
local notation "ar" => itemRaw C R symm Z shelf small orders home
local notation "zhead" => DescentOrdinarySignedWindows.header A native S ready names C marked census home
local notation "target" => DescentOrdinarySignedWindows.target A native S ready names home
/-- Every incidence count is kept below the signed formatter, including the
shared parallel serial at axis one. -/
def retainedRankField (s:SignedExtent) (base:ℕ) (x:Fin s.blocks) (axis:Fin 3) (j:Fin s.candidates) : Expr :=
  let core:=DescentOrdinarySignedParents.ROM.endAddress (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
  DescentOrdinarySignedAll.ranks core s.blocks s.candidates s.fieldBits s.lanes s.hosts s.groups x axis j
theorem phase_issued_ranks (input:(e₀).Input) (base:ℕ) (m:Memory w) (degree:input.newDegree=A.degree)
    (fits:(e₀).Fits input base w) (space:(e₀).roof base<2^w) (emit:DescentResetWindowFields.Emission A native C marked)
    (query:∀x p j f,Source (((e₀).layout input base).query x p j f) (fun h g=>Fused.columns (qr x p j h g) f) M ((e₀).installed input base m))
    (items:∀x p j t f,Source (((e₀).layout input base).items x p j t f) (fun h g=>Fused.columns (ar x p j t h g) f) M ((e₀).installed input base m))
    (header:∀x j,Source (((e₀).layout input base).header x j) (fun h g=>DescentResetFieldAssembler.raw b (zhead x j h g)) M ((e₀).installed input base m))
    (rawRoom:∀x j h g f,DescentResetFieldAssembler.digits (zhead x j h g) f<2^b)
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:breadth D*breadth D*Q≤2^b) (tickets:K≤2^b):
    (∀x p j,let field:=(e₀).retainedRankField base x p j
      field.Fits w ((e₀).roof base) ∧ Source field
        (fun h g=>(DescentOrdinarySignedRanks.result C census home (Stage.measured A native S ready) x p j h g:Cell b))
        M ((e₀).phaseImage input base m)) ∧
    ((e₀).phase input base w).Runs m ∧
    (∀x j,Reads ((e₀).page base x j) (fun h g=>DescentSignedCableCodec.encode (target x j h g)) M ((e₀).phaseImage input base m)) ∧
    (∀a,a<base ∨ (e₀).roof base≤a→(e₀).phaseImage input base m a=m a) ∧ CheapCode ((e₀).phase input base w).program:=by
  have enough:(e₀).phaseEnd base<2^w:=by rw [(e₀).calibrated base];exact space
  have total:=(e₀).phase_any input base w m fits enough
  have continued:=DescentOrdinarySignedDate.issued_ranks A native S ready names C marked R symm Z shelf small orders home
    ((e₀).layout input base) ((e₀).tailStart base) ((e₀).installed input base m) emit fits.header fits.query fits.items query items header rawRoom digits codes tickets enough
  have physical:=continued.2
  refine ⟨?_,total.1,?_,?_,total.2.2⟩
  · intro x p j
    have r:=continued.1 x p j
    rw [(e₀).phase_output input base m,degree,←(e₀).calibrated base]
    exact r
  · intro x j
    rw [(e₀).phase_output input base m,degree]
    exact physical.2.1 x j
  · intro a h;apply total.2.1 a
    simpa only [(e₀).calibrated base] using h

theorem phase_issued (input:(e₀).Input) (base:ℕ) (m:Memory w) (degree:input.newDegree=A.degree)
    (fits:(e₀).Fits input base w) (space:(e₀).roof base<2^w) (emit:DescentResetWindowFields.Emission A native C marked)
    (query:∀x p j f,Source (((e₀).layout input base).query x p j f) (fun h g=>Fused.columns (qr x p j h g) f) M ((e₀).installed input base m))
    (items:∀x p j t f,Source (((e₀).layout input base).items x p j t f) (fun h g=>Fused.columns (ar x p j t h g) f) M ((e₀).installed input base m))
    (header:∀x j,Source (((e₀).layout input base).header x j) (fun h g=>DescentResetFieldAssembler.raw b (zhead x j h g)) M ((e₀).installed input base m))
    (rawRoom:∀x j h g f,DescentResetFieldAssembler.digits (zhead x j h g) f<2^b)
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:breadth D*breadth D*Q≤2^b) (tickets:K≤2^b):
    ((e₀).phase input base w).Runs m ∧
    (∀x j,Reads ((e₀).page base x j) (fun h g=>DescentSignedCableCodec.encode (target x j h g)) M ((e₀).phaseImage input base m)) ∧
    (∀a,a<base ∨ (e₀).roof base≤a→(e₀).phaseImage input base m a=m a) ∧ CheapCode ((e₀).phase input base w).program:=by
  exact (phase_issued_ranks A native S ready names C marked R symm Z shelf small orders home input base m degree fits space emit query items header rawRoom digits codes tickets).2
end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
