import OAI.Hierarchy.DescentInstalledPublicHeader
import OAI.Hierarchy.DescentResetLocalOrder

namespace OAI
/-! # The original-edge tally of reset stems, hub limbs and contact wires -/
namespace Hierarchy.DescentSixParty.ResetInput.PublicCensus
open DescentResetTrunks DescentResetAttachments DescentRelativeContacts DescentCommonHost DescentDenseHostOrder
open DescentChosenRouter DescentResetCableSlots
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable {H M : ℕ} (vertex : Z.V↪Fin H) (key : A.graph.Edge↪Fin M)
local notation "W" => reenter Z T
local notation "R" => Z.placement
local notation "same" => funext (fun e=>(Z.allWidths e).symm)
local notation "wires" => installedWireNames A T.home (R).input T.hub same Z.bank Z.tables
local notation "lab" => fun t=>shortName T.commonDepth (T.code t)
local notation "legal" => fun t=>(T.codeLegal t).2
abbrev Cell := ℕ×ℕ
structure Tag where
  ordinal : ℕ
  src : Cell
  dst : Cell
  core : Bool
  deriving DecidableEq

/-- The host and the actual coarse block together identify a reset endpoint. -/
def tag : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool→Tag
  | (id,src,dst,x,y,_,mark)=>⟨id,(src,x),(dst,y),mark⟩

def stem (s : Bool) (i : A.graph.Edge) : Tag :=
  let t:=T.home (ends A.graph s i)
  let pos:=coarseName T.commonDepth (T.code t)
  ⟨(key i).val+M*(finTwoEquiv.symm s).val,
   (codeHost Z T vertex (.trunk s (lab t)),pos),
   (codeHost Z T vertex (publicNode (R) Z.graph T.commonDepth T.code s ((R).input s i)),pos),
   s || !(T.hub (T.home (A.graph.src i)))⟩

def trunk (t : Z.Fallback) : Tag :=
  let pos:=coarseName T.commonDepth (T.code t)
  ⟨2*M+(terminal vertex T.code legal t).val,(codeHost Z T vertex (.trunk false (lab t)),pos),
    (codeHost Z T vertex (.trunk true (lab t)),pos),!(T.hub t)⟩

def contactTag (c : (R).Contact) : Tag :=
  let pos:=(R).siteGroup T.commonDepth T.code ((R).owner false c)
  ⟨2*M+(H*(2^(Z.k+1)*(2^Z.n+1))+(contact (R) vertex T.code legal Ht T.bookHeight c).val),
    (codeHost Z T vertex (direct Z.graph false (linkSocket (R) lab T.commonDepth false c)),pos),
    (codeHost Z T vertex (direct Z.graph true (linkSocket (R) lab T.commonDepth true c)),pos),true⟩

abbrev Public := (Bool×A.graph.Edge) ⊕ (Z.Fallback ⊕ (R).Contact)

def parent : Public Z→(W).graph.Edge
  | .inl z=>(wires).symm (.inl z)
  | .inr (.inl t)=>(wires).symm (.inr (.inl t))
  | .inr (.inr c)=>(wires).symm (.inr (.inr (.inl c)))

def grains (test : Tag→Bool) (e : (W).graph.Edge) : ℕ :=
  let data:=actualFields Z T vertex key e
  if test (tag data) then data.2.2.2.2.2.1/Z.unit else 0

theorem stem_grains (test : Tag→Bool) (pos : 0<Z.unit) (s : Bool) (i : A.graph.Edge) :
    grains Z T vertex key test (parent Z T (.inl (s,i)))=(test (stem Z T vertex key s i)).toNat := by
  simp only [grains,parent,stemArchive,tag,stem,Nat.div_self pos]
  cases test _ <;> rfl

theorem trunk_grains (test : Tag→Bool) (pos : 0<Z.unit) (t : Z.Fallback) :
    grains Z T vertex key test (parent Z T (.inr (.inl t)))=
      if test (trunk Z T vertex (M:=M) t) then Fintype.card {i : A.graph.Edge // T.home (A.graph.dst i)=t} else 0 := by
  simp only [grains,parent,trunkArchive Z T vertex key t,tag,trunk,Nat.mul_div_cancel _ pos]
  rfl

theorem contact_grains (test : Tag→Bool) (pos : 0<Z.unit) (c : (R).Contact) :
    grains Z T vertex key test (parent Z T (.inr (.inr c)))=
      if test (contactTag Z T vertex (M:=M) c) then Fintype.card {i : A.graph.Edge // (R).contact i=c} else 0 := by
  simp only [grains,parent,contactArchive Z T vertex key c,tag,contactTag,Nat.mul_div_cancel _ pos]
  rfl

private theorem fiber_votes {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] (map : X→Y) (hit : Y→Bool) :
    (∑t : Y,if hit t then Fintype.card {j : X // map j=t} else 0)=∑i : X,(hit (map i)).toNat := by
  calc
    _=∑t : Y,∑j : {i : X // map i=t},(hit (map j.val)).toNat := by
      apply Finset.sum_congr rfl
      intro t _
      calc
        _ = ∑ _j : {i : X // map i=t},(hit t).toNat := by cases hit t <;> simp
        _ = _ := Finset.sum_congr rfl (fun j _=>by rw [j.property])
    _=_:=Fintype.sum_fiberwise map (fun i => (hit (map i)).toNat)

/-- This tally may select just one old chronological or source-relative
prefix, one signed endpoint, an unordered peer, or any intersection of those
predicates. Each old resident contributes exactly one vote per selected
polarity and one vote to each selected trunk and contact. -/
theorem counted (test : Tag→Bool) (pos : 0<Z.unit) :
    (∑p : Public Z,grains Z T vertex key test (parent Z T p))=
      (∑s : Bool,∑i : A.graph.Edge,(test (stem Z T vertex key s i)).toNat)+
      (∑i : A.graph.Edge,(test (trunk Z T vertex (M:=M) (T.home (A.graph.dst i)))).toNat)+
      ∑i : A.graph.Edge,(test (contactTag Z T vertex (M:=M) ((R).contact i))).toNat := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type,stem_grains _ _ _ _ _ pos,
    trunk_grains _ _ _ _ _ pos,contact_grains _ _ _ _ _ pos]
  rw [fiber_votes (fun i=>T.home (A.graph.dst i)) (fun t=>test (trunk Z T vertex (M:=M) t)),
      fiber_votes (R).contact (fun c=>test (contactTag Z T vertex (M:=M) c)),Nat.add_assoc]


/-- A loop contributes one incident grain at its site, as in the honest
unsigned slot before applying the outgoing/incoming sign bit. -/
def atSite (u : Cell) (x : Tag) : Bool := decide (x.src=u ∨ x.dst=u)

def peerPair (u v : Cell) (x : Tag) : Bool :=
  decide ((x.src=u ∧ x.dst=v) ∨ (x.src=v ∧ x.dst=u))

/-- Compare physical source coordinates first and the installed parent
ordinal inside a source. The dual polarization of a tether is immaterial
for the shared serial. -/
def earlier (siteOrder : Cell→ℕ) (query x : Tag) : Bool :=
  decide (siteOrder x.src<siteOrder query.src ∨ (x.src=query.src ∧ x.ordinal<query.ordinal))

def query (siteOrder : Cell→ℕ) (cut : Option Tag) (u : Cell) (peer : Option Cell) (x : Tag) : Bool :=
  (match cut with | none=>true | some q=>earlier siteOrder q x) &&
  (match peer with | none=>atSite u x | some v=>peerPair u v x)

theorem public_prefix (pos : 0<Z.unit) (siteOrder : Cell→ℕ) (cut : Option Tag) (u : Cell) (peer : Option Cell) :
    let hit:=query siteOrder cut u peer
    (∑p : Public Z,grains Z T vertex key hit (parent Z T p))=
      (∑s : Bool,∑i : A.graph.Edge,(hit (stem Z T vertex key s i)).toNat)+
      (∑i : A.graph.Edge,(hit (trunk Z T vertex (M:=M) (T.home (A.graph.dst i)))).toNat)+
      ∑i : A.graph.Edge,(hit (contactTag Z T vertex (M:=M) ((R).contact i))).toNat :=
  counted Z T vertex key _ pos


end
end Hierarchy.DescentSixParty.ResetInput.PublicCensus

end OAI
