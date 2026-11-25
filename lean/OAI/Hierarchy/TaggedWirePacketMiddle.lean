import OAI.Hierarchy.TaggedWirePacketCodes
import OAI.Hierarchy.TaggedWidePacketHidden
import OAI.Hierarchy.TaggedWireTransportAt
import OAI.Hierarchy.TaggedWirePacketPriorPort

namespace OAI
/-! # The one fixed intermediate bit ordering shared by both packet factors -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal.MotifOuterTerms Tagged AdaptiveProbe CalendarTape
open scoped Classical

variable {F : Type} [Field F] {S N H copies cap p e middle : ℕ} {row : Row F S H copies} {phys : Fin N→Chord S}

def bundleAddress {n : ℕ} (bits : Fin n→ℕ) (cap : ℕ) (fits : ∀i,bits i≤cap) :
    Bundle bits × Bool ↪ Fin ((n*2)*cap) where
  toFun x := finProdFinEquiv (halfCode x.1.1 x.2,x.1.2.castLE (fits x.1.1))
  inj' := by
    rintro ⟨⟨i,j⟩,b⟩ ⟨⟨q,r⟩,t⟩ eq
    obtain ⟨sides,digit⟩:=Prod.mk.inj (finProdFinEquiv.injective eq)
    obtain ⟨rfl,flags⟩:=Prod.mk.inj (finProdFinEquiv.injective sides)
    obtain rfl:=finTwoEquiv.symm.injective flags
    obtain rfl : j=r := Fin.ext (congrArg (fun u : Fin cap => u.val) digit)
    rfl

variable (R : RowRouting row phys) (c : Histogram (Fin H) copies) (s : Fin S)
local notation "old" => Installs.starts (source:=R.source) R.order
local notation "w" => Installs.numbered R.order (R.bits c)
local notation "win" => (Installs.packed (source:=R.source) R.order (R.bits c)).trans (R.shape c)

theorem middle_at (place : SiteBit (row.output c) s ↪ Fin middle) (y : State (row.output c) s)
    (a : SiteBit (row.output c) s) : packedMiddle c s place y (place a)=siteBits (row.output c) s y a := by
  let eqv := Equiv.ofInjective place place.injective
  have mem : place a∈Set.range place := ⟨a,rfl⟩
  change WidePadding.pad _ (fun i=>siteBits _ s y (eqv.symm i)) (place a)=_
  rw [WidePadding.pad,dite_eq_left mem]
  exact congrArg (siteBits _ s y) (eqv.symm_apply_apply a)

def middleRoom (roles cap : ℕ) := (roles*2)*cap

/-- The party state over the signed packet output is packed by original
role, side, and within-role digit, even when several roles share a chord. -/
def middlePlace (cap : ℕ) (fits : ∀i,w i≤cap) :
    SiteBit (row.output c) s ↪ Fin (middleRoom (Fintype.card R.Roles) cap) where
  toFun a := bundleAddress w cap fits ((NamedAperture.halfBits old w).symm
    ((NamedAperture.transport win).symm ⟨s,a⟩))
  inj' _ _ eq := by
    have d := (NamedAperture.transport win).symm.injective
      ((NamedAperture.halfBits old w).symm.injective ((bundleAddress w cap fits).injective eq))
    exact eq_of_heq (Sigma.mk.inj d).2

theorem middlePlace_read (cap : ℕ) (fits : ∀i,w i≤cap) (i) (j : Fin (w i)) (b : Bool)
    (here : (rowGraph old).vertex i b=s) :
    middlePlace R c s cap fits (NamedAperture.transportAt win
      (NamedAperture.atPort old w (PacketTurns.priorPort old w i j b here)))=
      finProdFinEquiv (halfCode i b,j.castLE (fits i)) := by
  let port:=PacketTurns.priorPort old w i j b here
  change bundleAddress w cap fits ((NamedAperture.halfBits old w).symm ((NamedAperture.transport win).symm
    ⟨s,NamedAperture.transportAt win (NamedAperture.atPort old w port)⟩))=_
  rw [←NamedAperture.transport_pair,Equiv.symm_apply_apply,←NamedAperture.at_half,Equiv.symm_apply_apply]
  rfl

/-- Exact active support of the fixed intermediate representation. Both the
current physical participant and the live width of this original role are
tested before a hidden digit is permitted to be nonzero. -/
theorem middle_range (cap : ℕ) (fits : ∀i,w i≤cap) (i : Fin (Fintype.card R.Roles)) (b : Bool) (j : Fin cap) :
    finProdFinEquiv (halfCode i b,j)∈Set.range (middlePlace R c s cap fits) ↔
      j.val<w i ∧ (rowGraph old).vertex i b=s := by
  constructor
  · rintro ⟨a,location⟩
    let z:=(NamedAperture.transport win).symm ⟨s,a⟩
    let raw:=(NamedAperture.halfBits old w).symm z
    have header : finProdFinEquiv (halfCode raw.1.1 raw.2,raw.1.2.castLE (fits raw.1.1))=
        finProdFinEquiv (halfCode i b,j) := location
    obtain ⟨code,digit⟩:=Prod.mk.inj (finProdFinEquiv.injective header)
    obtain ⟨item,side⟩:=Prod.mk.inj (finProdFinEquiv.injective code)
    have flag:=finTwoEquiv.symm.injective side
    have recovered : (NamedAperture.halfBits old w) raw=z := Equiv.apply_symm_apply _ _
    have mounted : NamedAperture.transport win z=⟨s,a⟩ := Equiv.apply_symm_apply _ _
    have here : (portGraph _).vertex (old raw.1.1) raw.2=s :=
      (NamedAperture.half_site old w raw.1 raw.2).symm.trans ((congrArg Sigma.fst recovered).trans
        ((NamedAperture.transport_site win z).symm.trans (congrArg Sigma.fst mounted)))
    have geom : (rowGraph old).vertex raw.1.1 raw.2=s := by
      cases eq:raw.2 <;> simpa [eq,rowGraph,portGraph,PortGraph.vertex] using here
    subst i
    subst b
    exact ⟨(congrArg Fin.val digit).symm.trans_lt raw.1.2.isLt,geom⟩
  · rintro ⟨live,here⟩
    let q : Fin (w i):=⟨j.val,live⟩
    exact ⟨_,(middlePlace_read R c s cap fits i q b here).trans
      (congrArg (fun z=>finProdFinEquiv (halfCode i b,z)) (Fin.ext rfl))⟩

theorem middle_bit (cap : ℕ) (fits : ∀i,w i≤cap) (y : State (row.output c) s) (i) (j : Fin (w i))
    (b : Bool) (here : (rowGraph old).vertex i b=s) :
    packedMiddle c s (middlePlace R c s cap fits) y (finProdFinEquiv (halfCode i b,j.castLE (fits i)))=
      rowBits old w (cast (congrArg (fun U=>State U s) (win).symm) y) (PacketTurns.priorPort old w i j b here) := by
  rw [←middlePlace_read R c s cap fits i j b here,middle_at,NamedAperture.rowBits_transport]

private abbrev DataShelf (p e : ℕ) := Fin (2^p) × Fin (2^e)

/-- The same static pin map is used on every histogram. The old sector
is addressed by its dense role/side ordinal; a new-sector lookup lands
at its own designated output port. -/
def packetData {V : Type} (roles cap : ℕ) (out : DataShelf p e→V) :
    DataShelf p e→V⊕Fin (middleRoom roles cap) := fun d=>
  if a : d.1.val<roles*2 then
    if j : d.2.val<cap then .inr (finProdFinEquiv (⟨d.1.val,a⟩,⟨d.2.val,j⟩)) else .inl (out d)
  else .inl (out d)

theorem packetData_old {V : Type} (cap : ℕ) (fits : ∀i,w i≤cap) (out : DataShelf p e→V)
    (i) (j : Fin (w i)) (b : Bool) (here : (rowGraph old).vertex i b=s) (d : DataShelf p e)
    (role : d.1.val=(halfCode i b).val) (digit : d.2.val=j.val) :
    packetData (Fintype.card R.Roles) cap out d=.inr (middlePlace R c s cap fits (NamedAperture.transportAt
      win (NamedAperture.atPort old w (PacketTurns.priorPort old w i j b here)))) := by
  rw [middlePlace_read]
  have h:=role.trans_lt (halfCode i b).isLt
  have g:=digit.trans_lt (j.isLt.trans_le (fits i))
  have first : (⟨d.1.val,h⟩ : Fin (Fintype.card R.Roles*2)) = halfCode i b := Fin.ext role
  have last : (⟨d.2.val,g⟩ : Fin cap) = j.castLE (fits i) := Fin.ext digit
  simp only [packetData,dite_eq_left h,dite_eq_left g,first,last]

theorem packetData_new {V : Type} {roles cap : ℕ} (out : DataShelf p e→V) (d : DataShelf p e)
    (new : roles*2≤d.1.val) : packetData roles cap out d=.inl (out d) := by
  simp [packetData,not_lt.mpr new]

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
