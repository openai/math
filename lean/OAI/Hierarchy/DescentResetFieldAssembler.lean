import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # Formatting each signed reset window from local endpoint classes and measured ranks -/
namespace Hierarchy.DescentResetFieldAssembler
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather
open scoped Classical Fin.CommRing
noncomputable section

structure Meta where
  live : Bool
  src : ℕ
  dst : ℕ
  here : ℕ
  selfAbsent : Bool
  core : Bool
  units : ℕ

def Meta.blank : Meta:=⟨false,0,0,0,false,false,0⟩

def digits (m : Meta) : Fin 7→ℕ:=![m.live.toNat,m.src,m.dst,m.here,m.selfAbsent.toNat,m.core.toNat,m.units]
def raw (b : ℕ) (m : Meta) : Cell (b*7):=encode b 7 (fun i=>(digits m i : Cell b))

def face (side : Bool) (m : Meta) : Bool:=m.live && decide ((if side then m.dst else m.src)=m.here)
def opposite (m : Meta) :=if m.src=m.here then m.dst else m.src
def peer (m : Meta) :=opposite m-(decide (m.selfAbsent=true ∧ m.here<opposite m)).toNat

/-- Keeping the measured rank argument separate allows all 16 formatters
to share the three previously issued native output banks. -/
def field (side : Bool) (which : Fin 8) (m : Meta) (rank : ℕ) :=
  if face side m then (![1,side.toNat,peer m,m.core.toNat,rank,rank,rank,m.units] : Fin 8→ℕ) which else 0

def decode (b : ℕ) (x : Cell (b*7)) : Meta :=
  let v:=(encode b 7).symm x
  ⟨decide ((v 0).val=1),(v 1).val,(v 2).val,(v 3).val,decide ((v 4).val=1),decide ((v 5).val=1),(v 6).val⟩

theorem decode_raw {b : ℕ} (m : Meta) (small : ∀i,digits m i<2^b) : decode b (raw b m)=m := by
  have eqn (i : Fin 7) : ((digits m i:ℕ):Cell b).val=digits m i:=Fin.val_cast_of_lt (small i)
  rcases m with ⟨live,src,dst,here,selfAbsent,core,units⟩
  simp only [decode,raw,Equiv.symm_apply_apply,eqn]
  cases live <;> cases selfAbsent <;> cases core <;> rfl

def kernel (b : ℕ) (side : Bool) (f : Fin 8) (x : Cell (b*7)) (y : Cell b) : Cell b :=
  field side f (decode b x) y.val

theorem blank (b : ℕ) (side : Bool) (f : Fin 8) : kernel b side f 0 0=0 := by
  have zero : (encode b 7).symm 0=fun _=>0 := by
    apply (encode b 7).injective
    rw [Equiv.apply_symm_apply]
    exact (DescentPacking.PackedMatch.Local.Gather.encode_zero b 7).symm
  simp [kernel,decode,zero,field,face]

def width (b M : ℕ):=(b*7+b)*M
def endAddress (base b M : ℕ):=base+32*2^(width b M)
def pair : (Fin 2×Fin 8)×Fin 2≃Fin 32:=(finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv
def code (side : Bool) : Fin 2:=⟨side.toNat,by cases side <;> decide⟩
def which (side : Bool) (f : Fin 8) (half : Fin 2):=pair ((code side,f),half)
def pages (b M : ℕ) (i : Fin 32) : Page :=
  let j:=pair.symm i
  binary (kernel b (decide (j.1.1.val=1)) j.1.2) M j.2
def tables (base b M : ℕ) (side : Bool) (f : Fin 8):=joined (pages b M) (width b M) base (which side f)
def atField (f : Fin 8) : Fin 3 := if f.val=5 then 1 else if f.val=6 then 2 else 0

theorem at_page (b M : ℕ) (side : Bool) (f : Fin 8) (half : Fin 2) :
    pages b M (which side f half)=binary (kernel b side f) M half :=by
  cases side <;> simp [pages,which,code]
theorem room (b M : ℕ) (i : Fin 32) : (pages b M i).bits ≤ width b M :=by
  obtain ⟨⟨⟨s,f⟩,j⟩,rfl⟩:=pair.surjective i
  fin_cases j
  · simpa [pages,binary,width] using Nat.mul_le_mul_right M (Nat.le_add_right (b*7) b)
  · simp [pages,binary,width]

variable {X K H G b M w : ℕ}
def fields (base b M : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr)
    (x : Fin X) (slot : Fin (2*K)) (f : Fin 8) : Expr :=
  let j : Fin 2×Fin K:=finProdFinEquiv.symm slot
  (tables base b M (decide (j.1.val=1)) f).read (header x j.2) (rank x (atField f) j.2)

def program (base b M w : ℕ):=mount (pages b M) (width b M) w base
def memory (base b M : ℕ) (m : Memory w):=after (pages b M) (width b M) base m

theorem any (base : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr) (m : Memory w)
    (early : ∀x j,(header x j).Fits w base) (prior : ∀x p j,(rank x p j).Fits w base) (space : endAddress base b M<2^w) :
    (program base b M w).Exec m (memory base b M m) (4+10*(32*2^(width b M))) ∧
    (∀x slot f,(fields base b M header rank x slot f).Fits w (endAddress base b M)) ∧
    (∀u,u<base ∨ endAddress base b M≤u→memory base b M m u=m u) ∧ CheapCode (program base b M w) := by
  have first:=DescentOrdinaryAtomFieldRAM.ROM.run (pages b M) (width b M) base m space
  refine ⟨first.1,?_,frame _ _ _ _,?_⟩
  · intro x slot f
    obtain ⟨⟨s,j⟩,rfl⟩:=finProdFinEquiv.surjective slot
    let side:=decide (s.val=1)
    let top:=endAddress base b M
    have lo : base≤top:=Nat.le_add_right ..
    have fit : DescentPackedZip.Fits (tables base b M side f) (header x j) (rank x (atField f) j) (b*7) b M top w :=
      ⟨ProtocolRAMGeneratedWrite.fits_mono _ lo (early x j),ProtocolRAMGeneratedWrite.fits_mono _ lo (prior x _ j),
        bank_room _ _ _ _ _ (room b M _) le_rfl space,bank_room _ _ _ _ _ (room b M _) le_rfl space,
        congrArg Page.bits (at_page b M side f 0),congrArg Page.bits (at_page b M side f 1)⟩
    simpa only [fields,Equiv.symm_apply_apply] using
      (show ((tables base b M side f).read (header x j) (rank x (atField f) j)).Fits w top
        from ⟨fit.apply,fit.right,fit.shift,fit.left⟩)
  · apply DescentOrdinaryAtomFieldRAM.ROM.cheap

theorem run (base : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr) (m : Memory w)
    (rawRow : Fin X→Fin K→Fin H→Fin G→Meta) (rankRow : Fin X→Fin 3→Fin K→Fin H→Fin G→Cell b)
    (early : ∀x j,(header x j).Fits w base) (prior : ∀x p j,(rank x p j).Fits w base)
    (input : ∀x j,Source (header x j) (fun h g=>raw b (rawRow x j h g)) M m)
    (offset : ∀x p j,Source (rank x p j) (rankRow x p j) M m)
    (small : ∀x j h g t,digits (rawRow x j h g) t<2^b) (space : endAddress base b M<2^w) :
    let done:=memory base b M m
    let top:=endAddress base b M
    (program base b M w).Exec m done (4+10*(32*2^(width b M))) ∧
    (∀x slot f,(fields base b M header rank x slot f).Fits w top) ∧
    (∀x slot f,let j : Fin 2×Fin K:=finProdFinEquiv.symm slot
      Source (fields base b M header rank x slot f) (fun h g=>
        (field (decide (j.1.val=1)) f (rawRow x j.2 h g) (rankRow x (atField f) j.2 h g).val : Cell b)) M done) ∧
    (∀u,u<base ∨ top≤u→done u=m u) ∧ DescentStaticWordColumn.names (program base b M w)=15*(32*2^(width b M)+1) ∧
      CheapCode (program base b M w) := by
  intro done top
  have init:=DescentOrdinaryAtomFieldRAM.ROM.run (pages b M) (width b M) base m space
  have stable:=frame (pages b M) (width b M) base m
  have lo : base≤top:=Nat.le_add_right ..
  have eqn (side : Bool) (f : Fin 8):=binary_mounted (kernel b side f) M (pages b M) (width b M) base m
    (room b M) (which side f) (at_page b M side f)
  have keep {d : ℕ} (op : Expr) (got : op.Fits w base) (v : Fin H→Fin G→Cell d) (source : Source op v M m) :
      Source op v M done :=fun j=>(ProtocolRAM.eval_below op _ m done got (fun u h=>stable u (.inl h))).trans (source j)
  have good (x : Fin X) (j : Fin K) (f : Fin 8) (side : Bool) :
      DescentPackedZip.Fits (tables base b M side f) (header x j) (rank x (atField f) j) (b*7) b M top w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ lo (early x j),ProtocolRAMGeneratedWrite.fits_mono _ lo (prior x _ j),
      bank_room _ _ _ _ _ (room b M _) le_rfl space,bank_room _ _ _ _ _ (room b M _) le_rfl space,
      congrArg Page.bits (at_page b M side f 0),congrArg Page.bits (at_page b M side f 1)⟩
  have all:=any base header rank m early prior space
  refine ⟨init.1,all.2.1,?_,stable,init.2,all.2.2.2⟩
  · intro x slot f
    obtain ⟨⟨s,j⟩,rfl⟩:=finProdFinEquiv.surjective slot
    let side:=decide (s.val=1)
    have got:=read_data _ _ _ top (good x j f side) (kernel b side f) (blank ..) done (eqn side f) _ _
      (keep _ (early x j) _ (input x j)) (keep _ (prior x (atField f) j) _ (offset x (atField f) j))
    have decoded (h g) : decode b (raw b (rawRow x j h g))=rawRow x j h g :=
      decode_raw _ (small x j h g)
    simpa only [fields,Equiv.symm_apply_apply,kernel,decoded] using got

end
end Hierarchy.DescentResetFieldAssembler

end OAI
