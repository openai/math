import OAI.Hierarchy.DescentDatedSignedWords
import OAI.Hierarchy.DescentDatedOrdinarySignedIssued
import OAI.Hierarchy.DescentOrdinaryRawFaces

namespace OAI
/-! # Decode the seven signed parent fields from the actual dated input pages -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty DescentSixParty.Chronology DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinarySignedMeta DescentOrdinarySignedRanks DescentResetFieldAssembler
open DescentPacking.PackedMatch.Local
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

local notation "RR" => Measured.roster C R symm Z
local notation "oldRaw" => Fused.fetched C R Z shelf small
open private DescentPacking.PackedMatch.Local.Gather.encode_zero DescentPacking.PackedMatch.Local.Gather.zero_fields from OAI.Hierarchy.DescentPackedFieldGather

private theorem readFits {tab : Tables} {u v : Expr} {a b n w out : ℕ}
    (tree : (tab.read u v).Fits w out) (shift : tab.shift.bits=a*n) (applyBits : tab.apply.bits=(a+b)*n) :
    DescentPackedZip.Fits tab u v a b n out w :=
  ⟨tree.2.2.2,tree.2.1,tree.2.2.1,tree.1,shift,applyBits⟩

private theorem memberFits {N w out : ℕ} (tab : Fin N→Tables) (columns : Fin N→Expr)
    (js : List (Fin N)) (fit : (Gather.collect tab columns js).Fits w out) (i : Fin N) (hi : i∈js) :
    (columns i).Fits w out ∧ (tab i).shift.Fits w out ∧ (tab i).apply.Fits w out := by
  induction js with
  | nil => simp at hi
  | cons j js ih =>
    rcases List.mem_cons.mp hi with eqn|mem
    · subst i
      exact ⟨fit.2.1,fit.2.2.1,fit.1⟩
    · exact ih fit.2.2.2 mem

section
variable {A native}

/-- The fixed raw operand at a padding host is the zero eleven-field row. -/
def signedRaw (x : Fin blocks) (j : Fin (breadth D*O)) (v : Fin H) (g : Fin groups) :=
  (home x v g).bind (fun h=>oldRaw h j)

def signedControls (x : Fin blocks) (j : Fin (breadth D*O)) (v : Fin H) (g : Fin groups) :=
  (home x v g).elim (DescentOrdinarySignedMeta.flags false false false false)
    (fun h=>controls C marked (resident ((RR).address h) j))

def signedUnits (x : Fin blocks) (j : Fin (breadth D*O)) (v : Fin H) (g : Fin groups) : Cell b :=
  (home x v g).elim 0 (fun h=>unitsCell C (resident ((RR).address h) j))

end

def signedPeer (x : Fin blocks) (j : Fin (breadth D*O)) (v : Fin H) (g : Fin groups) : Cell b :=
  (home x v g).elim 0 (fun h=>peerCell A native S ready names C h (resident ((RR).address h) j))

local notation "old₀" => signedRaw C R Z shelf small home
local notation "f₀" => signedControls C marked R symm Z home
local notation "u₀" => signedUnits (b:=b) C R symm Z home
local notation "p₀" => signedPeer (b:=b) A native S ready names C R symm Z home
variable (I : (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).Input) (base : ℕ) (m : Memory w)
local notation "sheet" => (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).installed I base m
variable (fits : (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).Fits I base w) (space : (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).roof base<2^w)
variable (mb : Fin blocks→Fin (breadth D*O)→Fin H→Fin groups→Cell 1)
  (oldBits : ∀x j, DescentPackedZip.Source (I.mark (x,j)) (mb x j) M m) (earlyBits : ∀z,(I.mark z).Fits w base)
  (known : ∀x j v g h,home x v g=some h→∀e : Local C h,(Measured.roster C R symm Z).address h e=j→
    ((mb x j v g).val=1 ↔ marked e.val))
  (oldFields : ∀x j f,DescentPackedZip.Source ((⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).rawField base (x,j) f)
    (fun v g=>Fused.columns (signedRaw C R Z shelf small home x j v g) f) M ((⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩ : SignedExtent).installed I base m))

section
variable {A native}

include fits space oldFields in
omit [Fintype E] in
theorem signed_gathered (x : Fin blocks) (j : Fin (breadth D*O)) :
    Source ((e₀).gathered base (x,j))
      (fun v g=>encode b 11 (Fused.columns (old₀ x j v g))) M sheet := by
  let z : Socket (e₀):=(x,j)
  let raw:=Fused.TablesROM.joins D Q K A.cap b M ((e₀).shapesStart base)
  let columns:=(e₀).rawField base z
  let expr:=(e₀).gathered base z
  have exprFit : expr.Fits w ((e₀).tailStart base) := (fits.header x j).2.2.2.2.2.2
  have gb : Gather.Bounds (d:=b) (M:=M) (w:=w) raw columns ((e₀).tailStart base) := by
    intro f
    have fit:=memberFits raw columns (List.finRange 11) exprFit f (List.mem_finRange f)
    have widths := Fused.TablesROM.shift_bits (D:=D) (Q:=Q) (K:=K) (L:=A.cap) (M:=M) (base:=(e₀).shapesStart base)
      (Gather.setField (d:=b) f) (f.castAdd 2) (Fused.TablesROM.insert_page f)
    exact ⟨fit.1,fit.2.1,fit.2.2,widths.1,widths.2⟩
  simpa only [expr,gathered,Gather.assembly,List.mem_finRange,ite_true] using
    Gather.collected raw columns ((e₀).tailStart base) gb sheet ((e₀).static_joins I base m fits space)
      (fun v g=>Fused.columns (old₀ x j v g)) (oldFields x j) (List.finRange 11)

include fits space earlyBits known oldBits oldFields in
theorem signed_flags (x : Fin blocks) (j : Fin (breadth D*O)) :
    Source ((e₀).flags I base (x,j)) (f₀ x j) M sheet ∧
    Source ((RawControls.unitsTable ((e₀).rawStart base) b b M).read ((e₀).gathered base (x,j)) (I.mark (x,j)))
      (u₀ x j) M sheet := by
  let z : Socket (e₀):=(x,j)
  let raw:=Fused.TablesROM.joins D Q K A.cap b M ((e₀).shapesStart base)
  let columns:= (e₀).rawField base z
  let expr:=(e₀).gathered base z
  let bits:=I.mark z
  let ftab:=RawControls.flagsTable ((e₀).rawStart base) b b M
  let utab:=RawControls.unitsTable ((e₀).rawStart base) b b M
  let bitsF:=ftab.read expr bits
  let bitsU:=utab.read expr bits
  have headerFit := fits.header x j
  have ff : bitsF.Fits w ((e₀).tailStart base) := headerFit.2.2.2
  have uf : bitsU.Fits w ((e₀).tailStart base) := headerFit.2.1.2.1
  let rows:=fun v g=>encode b 11 (Fused.columns (old₀ x j v g))
  have inputRows : Source expr rows M sheet := signed_gathered C R Z shelf small home I base m fits space oldFields x j
  have markBits : Source bits (mb x j) M sheet := fun r=>
    (ProtocolRAM.eval_below bits _ m sheet (earlyBits z) ((e₀).installed_words I base m fits space).2).trans
      (oldBits x j r)
  have fitF : DescentPackedZip.Fits ftab expr bits (b*11) 1 M ((e₀).tailStart base) w := readFits ff rfl rfl
  have fitU : DescentPackedZip.Fits utab expr bits (b*11) 1 M ((e₀).tailStart base) w := readFits uf rfl rfl
  have tables := (e₀).static_controls I base m fits space
  have fr:=read_data ftab expr bits _ fitF _ (by simp [rawFlags,activeRaw,DescentPacking.PackedMatch.Local.Gather.zero_fields])
    sheet tables.1 rows (mb x j) inputRows markBits
  have ur:=read_data utab expr bits _ fitU _ (by simp [rawUnits,activeRaw,DescentPacking.PackedMatch.Local.Gather.zero_fields])
    sheet tables.2 rows (mb x j) inputRows markBits
  have both (v g) : rawFlags (rows v g) (mb x j v g)=f₀ x j v g ∧
      rawUnits (b:=b) (rows v g) (mb x j v g)=u₀ x j v g := by
    cases h:home x v g with
    | none => simp [rows,signedRaw,signedControls,signedUnits,h,Fused.columns,rawFlags,rawUnits,activeRaw,flag_empty]
    | some who =>
      simpa only [rows,signedRaw,signedControls,signedUnits,h,Option.bind_some,Option.elim_some,controls,unitsCell] using
        funded_fields C R symm Z shelf small marked who j (mb x j v g) (known x j v g who h)
  exact ⟨(show (fun v g=>rawFlags (rows v g) (mb x j v g))=f₀ x j from funext fun v=>funext fun g=>(both v g).1) ▸ fr,
    (show (fun v g=>rawUnits (b:=b) (rows v g) (mb x j v g))=u₀ x j from funext fun v=>funext fun g=>(both v g).2) ▸ ur⟩

/-- The native first flag is one on exactly the occupied candidates. -/
theorem signed_flags_active (x : Fin blocks) (j : Fin (breadth D*O)) (v : Fin H) (g : Fin groups) :
    (f₀ x j v g).val≠0 ↔
      ((home x v g).any (fun h=>(resident ((RR).address h) j).isSome))=true := by
  cases pos:home x v g with
  | none => simp [signedControls,pos,flag_empty]
  | some h =>
    cases hit:resident ((RR).address h) j with
    | none => simp [signedControls,pos,controls,hit,flag_empty]
    | some e =>
      have nonzero (a b c : Bool) : (DescentOrdinarySignedMeta.flags true a b c).val≠0 := by
        intro zero
        have eqn : DescentOrdinarySignedMeta.flags true a b c=0 := Fin.ext zero
        have digit:=congrArg (fun v : Cell (1*4)=>(encode 1 4).symm v 0) eqn
        simp [DescentOrdinarySignedMeta.flags] at digit
        exact (by decide : (1 : Cell 1) ≠ 0)
          (digit.trans (congrFun (DescentPacking.PackedMatch.Local.Gather.zero_fields 1 4) 0))
      simp [signedControls,pos,controls,hit,nonzero]

end

theorem raw_header_lt (digitRoom : max (A.degree+1) (A.cap+1)<2^b)
    (x : Fin blocks) (j : Fin (breadth D*O)) (v : Fin H) (g : Fin groups) (f : Fin 7) :
    DescentResetFieldAssembler.digits (zhead x j v g) f<2^b := by
  have empty : DescentResetFieldAssembler.digits Meta.blank f<2^b := by
    fin_cases f <;> exact Nat.two_pow_pos _
  cases pos:home x v g with
  | none => simpa only [DescentOrdinarySignedWindows.header,pos,Option.elim_none] using empty
  | some h =>
    cases hit:resident ((census).addr h) j with
    | none =>
      simpa only [DescentOrdinarySignedWindows.header,pos,Option.elim_some,«meta»,hit,Option.elim_none] using empty
    | some e =>
      have degree : A.degree<2^b := (Nat.lt_succ_self A.degree).trans_le ((le_max_left ..).trans digitRoom.le)
      have nearWide := (DescentResetWindowFields.neighbor A native S ready names C h
        (residentFace A native C h e)).isLt.trans degree
      have unitsWide : C.count e.val<2^b := (Z.survives h e) ▸
        (Z.read h e).weight.isLt.trans_le ((le_max_right ..).trans digitRoom.le)
      have one : 1<2^b := lt_of_le_of_lt (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) (le_max_left ..)) digitRoom
      simp only [DescentOrdinarySignedWindows.header,pos,Option.elim_some,«meta»,hit,liveMeta]
      generalize (decide (C.src e.val=h))=src
      generalize (decide (C.dst e.val=h))=dst
      generalize (decide (marked e.val))=core
      cases src <;> cases dst <;> fin_cases f <;>
        simp_all [DescentResetFieldAssembler.digits,localWord,Bool.toNat] <;> split <;> omega

include fits space known earlyBits oldBits oldFields in
theorem signed_header_on (degree : I.newDegree=A.degree) (digitRoom : max (A.degree+1) (A.cap+1)<2^b)
    (peers : ∀x j,Source ((e₀).peerField I base (x,j)) (p₀ x j) M sheet)
    (x : Fin blocks) (j : Fin (breadth D*O)) :
    Source (((e₀).layout I base).header x j)
      (fun v g=>DescentResetFieldAssembler.raw b (zhead x j v g)) M sheet := by
  let z:Socket (e₀):=(x,j)
  let pairBank:=pairTable ((e₀).metaStart base) I.newDegree b M
  let formatBank:=metaTable ((e₀).metaStart base) I.newDegree b M
  let f:=(e₀).flags I base z
  let u:=(RawControls.unitsTable ((e₀).rawStart base) b b M).read ((e₀).gathered base z) (I.mark z)
  let p:=(e₀).peerField I base z
  let bound:=(e₀).tailStart base
  obtain ⟨readF,readU⟩:=signed_flags C marked R symm Z shelf small home I base m fits space mb
      oldBits earlyBits known oldFields x j
  have readP : Source p (p₀ x j) M sheet := peers x j
  have root:=fits.header x j
  have pairOk : DescentPackedZip.Fits pairBank p u b b M bound w := readFits root.2.1 rfl rfl
  have formatOk : DescentPackedZip.Fits formatBank f (pairBank.read p u) (1*4) (b*2) M bound w :=
    readFits root rfl rfl
  have tables:= (e₀).static_formatter I base m fits space
  have words:=read_data pairBank p u bound pairOk (DescentOrdinarySignedMeta.pair b) (pair_empty b) sheet tables.1
    (p₀ x j) (u₀ x j) readP readU
  have compiled:=read_data formatBank f (pairBank.read p u) bound formatOk (format I.newDegree b) (format_empty I.newDegree b)
    sheet tables.2 (f₀ x j) _ readF words
  convert compiled using 1
  · rfl
  funext v g
  cases pos:home x v g with
  | none =>
    simp [DescentOrdinarySignedWindows.header,signedControls,signedPeer,signedUnits,pos,flag_empty,pair_empty,format_empty,raw_empty]
  | some h =>
    cases hit:resident ((RR).address h) j with
    | none =>
      simp [DescentOrdinarySignedWindows.header,DescentOrdinarySignedMeta.meta,Incidence.of_measured,
        signedControls,signedPeer,signedUnits,pos,hit,controls,unitsCell,peerCell,flag_empty,pair_empty,format_empty,raw_empty]
    | some e =>
      have nearWide := (DescentResetWindowFields.neighbor A native S ready names C h
        (residentFace A native C h e)).isLt.trans (lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left ..).trans digitRoom.le))
      have unitsWide : C.count e.val<2^b := (Z.survives h e) ▸
        (Z.read h e).weight.isLt.trans_le ((le_max_right ..).trans digitRoom.le)
      simp only [DescentOrdinarySignedWindows.header,DescentOrdinarySignedMeta.meta,Incidence.of_measured,
        signedControls,signedPeer,signedUnits,pos,Option.elim_some,hit,controls,unitsCell,peerCell,format_inputs,ite_true,
        liveMeta,Fin.val_cast_of_lt nearWide,Fin.val_cast_of_lt unitsWide,degree]

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
