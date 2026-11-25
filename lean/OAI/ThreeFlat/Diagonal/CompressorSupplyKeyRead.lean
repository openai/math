import OAI.ThreeFlat.Diagonal.CompressorSupplyOrigins
import OAI.ThreeFlat.Diagonal.CompressorPhysicalKeyRow

namespace OAI
/-! # Numeric source base and materialized successor key of a typed crossing -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement Graph
open scoped Fin.NatCast Classical

variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {w n N t l : ℕ}
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l) (b : B ≃ Fin N)
variable (ptr : F n) (data : Param → Word w) (mem : Memory w) (vs : Fin n → Word w)
local notation "V" => Formula.value data mem vs
local notation "o" => Demand.formulaOps n
local notation "g" => oldColumns o ptr
local notation "rad" => radices o ptr S

private theorem wordMap : OpMap o (words mem) V where
  lit _ := rfl
  bin _ _ _ := rfl
  load _ := rfl
  choose _ _ _ _ := by simp [Demand.formulaOps,words,Formula.value,Comparison.test]

private theorem site_map (a : RoleSites (F n)) (i : Fin 3) :
    (Graph.siteAt a i).map V=Graph.siteAt (a.map V) i := by fin_cases i <;> rfl

private theorem key_map (z : Ends (F n)) (s : RoleSites (F n)) (h k : Fin 3) (kind : Fin 4)
    (copy : Fin (S.pieces kind)) :
    V (Graph.encodeCandidate o rad S (Graph.siteAt s h) z s h k kind copy).key =
      (Graph.encodeCandidate (words mem) ((rad).map V) S (Graph.siteAt (s.map V) h)
        (z.map V) (s.map V) h k kind copy).key := by
  have hm:=wordMap data mem vs
  fin_cases h <;>
    simp [Graph.encodeCandidate,Graph.encodeBase,Graph.siteAt,hm.bin,hm.lit,hm.digit,hm.choose,
      Radices.map,Ends.map,Placement.Site.map,Position.map,RoleSites.map]

theorem crossing_identifiers (R : ArcReads P E ((g).map V) mem)
    (num : ∀x,E.base x=((b x).val:Word w)) (bound : ∀k,S.pieces k≤S.pieceRadix)
    (rr : (rad).map V=rowRadices (w:=w) (t:=t) (l:=l) S) (lay : Bool) (hc : 2≤S.colors)
    (motif : P.Motif) (e : Ends (F n)) (enc : e.map V=encodeEnds P E motif.val)
    (kind : Fin 4) (copy : Fin (S.pieces kind)) :
    let z : ShrinkEdge P S.pieces:=⟨kind,normalize P motif,copy⟩
    let u:=(ordinalOf S P (baseNat b) bound lay false hc) z
    V (crossingBase ptr S lay e kind)=((Template.tagNumber b u.1).val:Word w) ∧
    V (crossingKey ptr S lay e kind copy)=(edgeId S P (baseNat b) bound z:Word w) := by
  let z : ShrinkEdge P S.pieces:=⟨kind,normalize P motif,copy⟩
  let u:=(ordinalOf S P (baseNat b) bound lay false hc) z
  let sites:=roleSites o g S.degree lay e
  let role:=baseRole lay false kind
  have hm:=wordMap data mem vs
  have geom : sites.map V = roleSites (words mem) ((g).map V) S.degree lay (encodeEnds P E motif.val) := by
    rw [show sites.map V=_ from hm.parties g S.degree lay e,enc]
  have rrk : (Graph.roles lay kind).1=roleNumber role := by
    simpa only [Bool.false_eq_true,ite_false] using roleIndex lay false kind
  have src : (crossingSite ptr S lay e kind).map V=siteCode E (siteOf P lay role motif) := by
    change (Graph.siteAt sites _).map V=_
    rw [site_map,geom,rrk]
    exact actualRole S P E _ mem R lay motif role
  have first : u.1=base (siteOf P lay role motif) := normalize_base S P lay role motif
  constructor
  · have mapped : V (crossingBase ptr S lay e kind)=Graph.encodeBase (words mem) ((rad).map V)
        ((crossingSite ptr S lay e kind).map V) := by
      simp only [crossingBase,Graph.encodeBase,hm.digit,Radices.map,Placement.Site.map]
    rw [mapped,rr,src,first]
    change baseAddress S E (base (siteOf P lay role motif)) = _
    exact Template.packed_word S b E num (base (siteOf P lay role motif))
  · change V (Graph.encodeCandidate o rad S (Graph.siteAt sites (Graph.roles lay kind).1) e sites _ _ kind copy).key=_
    rw [key_map,rr,geom,enc]
    let s:=roleSites (words mem) ((g).map V) S.degree lay (encodeEnds P E motif.val)
    have valid : s.valid=1 := congrArg RoleSites.valid (roles_code R lay motif)
    have ident:=encode_identifier S P E (baseNat b) bound num mem motif kind copy
    change (Graph.encodeCandidate (words mem) (rowRadices (w:=w) (t:=t) (l:=l) S) S
      (Graph.siteAt s (Graph.roles lay kind).1) (encodeEnds P E motif.val) s
      (Graph.roles lay kind).1 (Graph.roles lay kind).2 kind copy).key=_
    simpa only [Graph.encodeCandidate,valid,words,Nat.cast_one,eq_self,ite_true] using ident


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
