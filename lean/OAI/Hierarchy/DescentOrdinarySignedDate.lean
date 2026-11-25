import OAI.Hierarchy.DescentOrdinaryParentWordRAM
import OAI.Hierarchy.DescentOrdinarySignedEmission

namespace OAI
/-! A fixed public date installs the original donor record converter, executes
the comparison scans and publishes every signed cable chip. -/
namespace Hierarchy.DescentOrdinarySignedDate
open DescentSixParty DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F Pin U J E X T V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype E] [Fintype X] [Fintype T]
  {d k i D Q O K b M hosts groups blocks oldH w:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ}
local notation "P" => breadth D
structure Layout (blocks c:ℕ) where
  header:Fin blocks→Fin c→Expr
  query:Fin blocks→Fin 3→Fin c→Fin 11→Expr
  items:Fin blocks→Fin 3→Fin c→Fin c→Fin 11→Expr

namespace Layout
variable {c : ℕ}
variable (Z:Layout blocks c) (base D Q K L b M:ℕ)
local notation "convert" => DescentOrdinarySignedParents.ROM.expression base D Q K L b M
local notation "afterROM" => DescentOrdinarySignedParents.ROM.endAddress base D Q K L b M

def qword (x:Fin blocks) (p:Fin 3) (j:Fin c):=convert (Z.query x p j)
def aword (x:Fin blocks) (p:Fin 3) (j t:Fin c):=convert (Z.items x p j t)
local notation "query₀" => qword Z base D Q K L b M
local notation "items₀" => aword Z base D Q K L b M
def endAddress (_degree H groups:ℕ):=DescentOrdinarySignedAll.endAddress afterROM blocks c L b M H groups
def program (degree H groups w:ℕ):=
  (DescentOrdinarySignedParents.ROM.program base D Q K L b M w).seq
    (DescentOrdinarySignedAll.program afterROM Z.header query₀ items₀ degree L b M H groups w)
def memory (degree H groups:ℕ) (m:Memory w):=
  DescentOrdinarySignedAll.memory afterROM Z.header query₀ items₀ degree L b M H groups
    (DescentOrdinarySignedParents.ROM.memory base D Q K L b M m)
def time (degree H groups:ℕ):=DescentOrdinarySignedParents.ROM.time D Q K L b M+
  DescentOrdinarySignedAll.time afterROM Z.header query₀ items₀ degree L b M H groups
def output (x:Fin blocks) (j:Fin (2*L)) (H groups:ℕ):=
  DescentOrdinarySignedAll.page afterROM blocks c L b M H groups x j
theorem any (degree H groups w:ℕ) (m:Memory w)
    (hf:∀x j,(Z.header x j).Fits w base)
    (qf:∀x p j f,(Z.query x p j f).Fits w base) (af:∀x p j t f,(Z.items x p j t f).Fits w base)
    (space:DescentOrdinarySignedAll.endAddress afterROM blocks c L b M H groups<2^w):
    let end':=DescentOrdinarySignedAll.endAddress afterROM blocks c L b M H groups
    let done:=memory Z base D Q K L b M degree H groups m
    (program Z base D Q K L b M degree H groups w).Exec m done (time Z base D Q K L b M degree H groups) ∧
    (∀u,u<base ∨ end'≤u→done u=m u) ∧ CheapCode (program Z base D Q K L b M degree H groups w):=by
  intro end' done
  have ranges:=DescentOrdinarySignedAll.ordered (X:=blocks) (K:=c) (cap:=L) (b:=b) (M:=M) (H:=H) (gg:=groups) afterROM
  have top:=ranges.1.trans ranges.2
  have floor:base≤afterROM:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have boot:=DescentOrdinarySignedParents.ROM.setup base D Q K L b M m (top.trans_lt space)
  have rest:=DescentOrdinarySignedAll.any afterROM Z.header query₀ items₀ degree L b M H groups (DescentOrdinarySignedParents.ROM.memory base D Q K L b M m)
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ floor (hf x j))
    (fun x p j=>DescentOrdinarySignedParents.ROM.fits base _ (qf x p j) (top.trans_lt space))
    (fun x p j t=>DescentOrdinarySignedParents.ROM.fits base _ (af x p j t) (top.trans_lt space)) space
  refine ⟨Procedure.Exec.then boot.1 rest.1,?_,cheap_seq boot.2.2.2.2 rest.2.2⟩
  intro u h;rcases h with low|high
  · exact (rest.2.1 u (.inl (low.trans_le floor))).trans (boot.2.2.2.1 u (.inl low))
  · exact (rest.2.1 u (.inr high)).trans (boot.2.2.2.1 u (.inr (top.trans high)))

end Layout
local notation "c" => breadth D*O

variable (A:GroupStage W G price ε J U k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule)
  (ready:A.StateBounds S i) (names:Stage.Host J U k↪ℕ)
  (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u p,R v p=some u→∃z,R u z=some v)
  (Z:Measured C R X T V Q O K A.cap) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K A.cap) f,Machine.fields R (Z.venue h) path (Z.loc x).1 s f<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
  (home:Fin blocks→Fin hosts→Fin groups→Option (Stage.Host J U k)) (layout:Layout blocks (breadth D * O)) (base:ℕ)
local notation "census" => Incidence.of_measured C R symm Z orders
local notation "qr" => queryRaw C R symm Z shelf small orders home
local notation "ar" => itemRaw C R symm Z shelf small orders home
local notation "zhead" => DescentOrdinarySignedWindows.header A native S ready names C marked census home
local notation "target" => DescentOrdinarySignedWindows.target A native S ready names home
local notation "next" => DescentOrdinarySignedParents.ROM.endAddress base D Q K A.cap b M
local notation "end'" => DescentOrdinarySignedAll.endAddress next blocks c A.cap b M hosts groups
local notation "query₀" => Layout.qword layout base D Q K A.cap b M
local notation "items₀" => Layout.aword layout base D Q K A.cap b M

/-- The live words below are the original eleven raw donor observations, before
the receiver decides membership, parallel class, or any of the signed slots. -/
theorem issued_ranks (m:Memory w) (emit:DescentResetWindowFields.Emission A native C marked)
    (hf:∀x j,(layout.header x j).Fits w base)
    (qf:∀x p j f,(layout.query x p j f).Fits w base) (af:∀x p j t f,(layout.items x p j t f).Fits w base)
    (hq:∀x p j f,DescentPackedZip.Source (layout.query x p j f) (fun v g=>Fused.columns (qr x p j v g) f) M m)
    (ha:∀x p j t f,DescentPackedZip.Source (layout.items x p j t f) (fun v g=>Fused.columns (ar x p j t v g) f) M m)
    (hd:∀x j,DescentPackedZip.Source (layout.header x j) (fun v g=>DescentResetFieldAssembler.raw b (zhead x j v g)) M m)
    (rawRoom:∀x j h g f,DescentResetFieldAssembler.digits (zhead x j h g) f<2^b)
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:P*P*Q≤2^b) (tickets:K≤2^b) (space:end'<2^w):
    let done:=Layout.memory layout base D Q K A.cap b M A.degree hosts groups m
    (∀x p j,let e:=DescentOrdinarySignedAll.ranks next blocks c b M hosts groups x p j
      e.Fits w end' ∧ DescentPackedZip.Source e
        (fun h g=>(DescentOrdinarySignedRanks.result C census home (Stage.measured A native S ready) x p j h g:Cell b)) M done) ∧
    (Layout.program layout base D Q K A.cap b M A.degree hosts groups w).Exec m done
      (Layout.time layout base D Q K A.cap b M A.degree hosts groups) ∧
    (∀x j,Reads (DescentOrdinarySignedAll.page next blocks c A.cap b M hosts groups x j)
      (fun v g=>DescentSignedCableCodec.encode (target x j v g)) M done) ∧
    (∀u,u<base ∨ end'≤u→done u=m u) ∧ CheapCode (Layout.program layout base D Q K A.cap b M A.degree hosts groups w):=by
  intro done
  let mid:=DescentOrdinarySignedParents.ROM.memory base D Q K A.cap b M m
  have top:next≤end':=(DescentOrdinarySignedAll.ordered (X:=blocks) (K:=c) (cap:=A.cap) (b:=b) (M:=M) (H:=hosts) (gg:=groups) next).1.trans
    (DescentOrdinarySignedAll.ordered (X:=blocks) (K:=c) (cap:=A.cap) (b:=b) (M:=M) (H:=hosts) (gg:=groups) next).2
  have floor:base≤next:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have boot:=DescentOrdinarySignedParents.ROM.setup base D Q K A.cap b M m (top.trans_lt space)
  have request (x p j):=(DescentOrdinarySignedParents.ROM.source base (layout.query x p j) m R (qr x p j) (qf x p j) (hq x p j) (top.trans_lt space))
  have item (x p j t):=(DescentOrdinarySignedParents.ROM.source base (layout.items x p j t) m R (ar x p j t) (af x p j t) (ha x p j t) (top.trans_lt space))
  have head (x j):DescentPackedZip.Source (layout.header x j) (fun h g=>DescentResetFieldAssembler.raw b (zhead x j h g)) M mid:=
    fun r=>(ProtocolRAM.eval_below (layout.header x j) _ m mid (hf x j) (fun a before=>boot.2.2.2.1 a (.inl before))).trans (hd x j r)
  have one:1<2^b:=(show 1≤A.cap+1 by omega).trans_lt ((le_max_right _ _).trans_lt digits)
  have mass:A.cap<2^b:=(Nat.le_succ _).trans_lt ((le_max_right _ _).trans_lt digits)
  let peerCode:=fun h (e:Local C h)=>((Measured.roster C R symm Z).entry h e).peer.val
  have same (h) (e f:Local C h):peerCode h e=peerCode h f ↔ other C h e=other C h f:=
    Fin.ext_iff.symm.trans (Measured.samePeer C R symm Z h e f)
  have continued:=DescentOrdinarySignedAll.issued_ranks next layout.header query₀ items₀ A native S ready names C marked census peerCode home
    mid emit same (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ floor (hf x j))
    (fun x p j=>(request x p j).1) (fun x p j t=>(item x p j t).1)
    (fun x p j=>by simpa only [Layout.qword, mid, peerCode, queryCode C R symm Z shelf small orders home] using (request x p j).2)
    (fun x p j t=>by simpa only [Layout.aword, mid, peerCode, itemCode C R symm Z shelf small orders home] using (item x p j t).2)
    head (fun x p j h g=>by rw [←queryCode C R symm Z shelf small orders home];exact fits _ one codes tickets mass)
    (fun x p j t h g=>by rw [←itemCode C R symm Z shelf small orders home];exact fits _ one codes tickets mass) rawRoom digits space
  have finish:=continued.2
  refine ⟨continued.1,Procedure.Exec.then boot.1 finish.1,finish.2.1,?_,cheap_seq boot.2.2.2.2 finish.2.2.2⟩
  intro u h;rcases h with low|high
  · exact (finish.2.2.1 u (.inl (low.trans_le floor))).trans (boot.2.2.2.1 u (.inl low))
  · exact (finish.2.2.1 u (.inr high)).trans (boot.2.2.2.1 u (.inr (top.trans high)))
theorem issued (m:Memory w) (emit:DescentResetWindowFields.Emission A native C marked)
    (hf:∀x j,(layout.header x j).Fits w base)
    (qf:∀x p j f,(layout.query x p j f).Fits w base) (af:∀x p j t f,(layout.items x p j t f).Fits w base)
    (hq:∀x p j f,DescentPackedZip.Source (layout.query x p j f) (fun v g=>Fused.columns (qr x p j v g) f) M m)
    (ha:∀x p j t f,DescentPackedZip.Source (layout.items x p j t f) (fun v g=>Fused.columns (ar x p j t v g) f) M m)
    (hd:∀x j,DescentPackedZip.Source (layout.header x j) (fun v g=>DescentResetFieldAssembler.raw b (zhead x j v g)) M m)
    (rawRoom:∀x j h g f,DescentResetFieldAssembler.digits (zhead x j h g) f<2^b)
    (digits:max (A.degree+1) (A.cap+1)<2^b) (codes:P*P*Q≤2^b) (tickets:K≤2^b) (space:end'<2^w):
    let done:=Layout.memory layout base D Q K A.cap b M A.degree hosts groups m
    (Layout.program layout base D Q K A.cap b M A.degree hosts groups w).Exec m done
      (Layout.time layout base D Q K A.cap b M A.degree hosts groups) ∧
    (∀x j,Reads (DescentOrdinarySignedAll.page next blocks c A.cap b M hosts groups x j)
      (fun v g=>DescentSignedCableCodec.encode (target x j v g)) M done) ∧
    (∀u,u<base ∨ end'≤u→done u=m u) ∧ CheapCode (Layout.program layout base D Q K A.cap b M A.degree hosts groups w):=by
  exact (issued_ranks A native S ready names C marked R symm Z shelf small orders home layout base m emit hf qf af hq ha hd rawRoom digits codes tickets space).2
end
end Hierarchy.DescentOrdinarySignedDate

end OAI
