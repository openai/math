import OAI.Hierarchy.DescentTerminalGraphRows
import OAI.Hierarchy.DescentTerminalRowBooks
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Building both terminal row orders from the actual graph incidence lists -/

namespace Hierarchy.DescentTerminalGraphPositions
open Computability.BorderVNP.Crossing DescentKernelHistory DescentTerminalRecipeRows DescentTerminalBinReaddress
open DescentTerminalGraphRows (Part)
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

/-- Number the supplied labels by their true increasing rank. -/
def ordered {X : Type} [Fintype X] (rank : X ↪ ℕ) : X ≃ Fin (Fintype.card X) :=
  let keys := Finset.univ.image rank
  let into : X ≃ keys := Equiv.ofBijective (fun x=>⟨rank x,Finset.mem_image_of_mem rank (Finset.mem_univ _)⟩) ⟨
    (fun a b h=>rank.injective (congrArg Subtype.val h)),
    (fun y=>by obtain ⟨x,_,hx⟩ := Finset.mem_image.mp y.2; exact ⟨x,Subtype.ext hx⟩)⟩
  into.trans (keys.orderIsoOfFin ((Finset.card_image_of_injective _ rank.injective).trans (by simp))).toEquiv.symm

variable {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)
abbrev Names (p : ℕ) := ((e : N.Edge) × Fin (poolBatchCount (N.width e) p)) ⊕
  ((z : P) × Fin (poolBatchCount (bits z) p))

def name {v : N.Site} : Part N p v → Names N p
  | ⟨.inl e,j⟩=>.inl ⟨e.1,j⟩
  | ⟨.inr port,j⟩=>.inr ⟨port.1,j⟩

/-- Only the control-construction layer ever sees graph-wide identifiers.
The scalar menu uses local port and operand ordinals exclusively. -/
structure Order (S p : ℕ) where
  home : N.Site→Fin S
  nodeRank : N.Site ↪ ℕ
  wireRank : Names N p ↪ ℕ
  operandRank : ∀v,Boundary N v ↪ ℕ

namespace Order
variable {N} (L : Order N S p)
abbrev Nodes (i : Fin S) := {v : N.Site // L.home v=i}
def nodes (i : Fin S) := ordered ((Function.Embedding.subtype (fun v=>L.home v=i)).trans L.nodeRank)

def neighbor (i : Fin S) : Names N p→Option (Fin S)
  | .inl ⟨e,_⟩ => some (if L.home (N.src e)=i then L.home (N.dst e) else L.home (N.src e))
  | .inr _ => none

def Used (i : Fin S) (nm : Names N p) := ∃ v : Nodes L i, ∃ u : Part N p v.val,name N u=nm

abbrev Group (i : Fin S) := {g : Option (Fin S) // ∃ nm,Used L i nm ∧ neighbor L i nm=g}
abbrev At (i : Fin S) (g : Group L i) := {nm : Names N p // Used L i nm ∧ neighbor L i nm=g.val}
def neighborCode : Option (Fin S) ↪ ℕ where
  toFun z:=z.elim 0 (fun i=>i.val+1)
  inj' := by
    rintro (_|a) (_|b) h
    · rfl
    · simp at h
    · simp at h
    · exact congrArg some (Fin.ext (Nat.add_right_cancel h))

/-- The exterior group comes first, followed by the neighboring home
ordinals in increasing order. Empty groups reserve no descriptor rows. -/
def groups (i : Fin S) := ordered ((Function.Embedding.subtype _).trans neighborCode : Group L i ↪ ℕ)
def inGroup (i : Fin S) (g : Group L i) :=
  ordered ((Function.Embedding.subtype _).trans L.wireRank : At L i g ↪ ℕ)
def size (i : Fin S) (g : Fin (Fintype.card (Group L i))) := Fintype.card (At L i ((groups L i).symm g))

def catalog (i : Fin S) : ((g : Fin (Fintype.card (Group L i))) × Fin (size L i g)) ↪ Names N p where
  toFun a := (((inGroup L i ((groups L i).symm a.1)).symm a.2).val)
  inj' := by
    rintro ⟨g,a⟩ ⟨k,b⟩ h
    have lg := ((inGroup L i ((groups L i).symm g)).symm a).property.2
    have lk := ((inGroup L i ((groups L i).symm k)).symm b).property.2
    have eqGroup : g=k := (groups L i).symm.injective (Subtype.ext
      (lg.symm.trans ((congrArg (neighbor L i) h).trans lk)))
    subst k
    exact congrArg (Sigma.mk g) ((inGroup L i _).symm.injective (Subtype.ext h))

def node (i : Fin S) (v : Fin (Fintype.card (Nodes L i))) := ((nodes L i).symm v).val
def arity (i : Fin S) (v : Fin (Fintype.card (Nodes L i))) := DescentTerminalGraphRows.arity N p (node L i v)
def args (i : Fin S) (v : Fin (Fintype.card (Nodes L i))) (j : Fin (arity L i v)) :=
  name N ((DescentTerminalGraphRows.number N p (node L i v) (L.operandRank _)).symm j)

theorem covered (i : Fin S) (v : Fin (Fintype.card (Nodes L i))) (j : Fin (arity L i v)) :
    ∃r,catalog L i r=args L i v j := by
  let nm := args L i v j
  have used : Used L i nm := ⟨(nodes L i).symm v,_,rfl⟩
  let g : Group L i := ⟨neighbor L i nm,nm,used,rfl⟩
  let k := groups L i g
  have gk : (groups L i).symm k=g := (groups L i).symm_apply_apply _
  let entry : At L i ((groups L i).symm k) := ⟨nm,used,by rw [gk]⟩
  refine ⟨⟨k,inGroup L i _ entry⟩,?_⟩
  exact congrArg Subtype.val ((inGroup L i _).symm_apply_apply entry)

def site (i : Fin S) : Site := Site.ofNames (size L i) (catalog L i) (arity L i) (args L i) (covered L i)

theorem catalog_arg (i : Fin S) (v : Fin ((site L i).nodes)) (j : Fin ((site L i).arity v)) :
    catalog L i ((site L i).arg v j)=args L i v j :=
  (Site.ofNames_arg (size L i) (catalog L i) (arity L i) (args L i) (covered L i) v j _).mp rfl

def readName (a : N.Assignment) (x : Ports bits) : Names N p→Fin p→Bool
  | .inl ⟨e,k⟩=>TaggedShorterFields.slice p (a e) k.val
  | .inr ⟨port,k⟩=>TaggedShorterFields.slice p (x port) k.val

omit [Fintype P] in
theorem read_name (a : N.Assignment) (x : Ports bits) {v : N.Site} (u : Part N p v) :
    readName (N:=N) a x (name N u)=DescentTerminalGraphRows.readPart N p a x u := by
  rcases u with ⟨e|port,j⟩ <;> rfl

variable {W q piece : ℕ} (positive : 0<W) (slotPositive : 0<q)
    (payloadWidth : p=W*piece)

def payload (a : N.Assignment) (x : Ports bits) :
    Fin (Bins (W:=W) (q:=q) (site L))→Payload W q piece :=
  let row (z : Named (site L)) :=
    fun j : Fin (W*piece) => readName (N:=N) a x (catalog L z.1 z.2) (j.cast payloadWidth.symm)
  Function.curry (Function.extend (source (site L) positive slotPositive) row (fun _ _=>false))

theorem payload_source (a : N.Assignment) (x : Ports bits) (z : Named (site L)) (j : Fin (W*piece)) :
    let src := source (site L) positive slotPositive z
    payload L positive slotPositive payloadWidth a x src.1 src.2 j=
      readName (N:=N) a x (catalog L z.1 z.2) (j.cast payloadWidth.symm) := by
  intro src
  let nameRow (y : Named (site L)) (d : Fin (W*piece)) := readName (N:=N) a x (catalog L y.1 y.2) (d.cast payloadWidth.symm)
  change Function.extend (source (site L) positive slotPositive) nameRow (fun _ _=>false)
    (source (site L) positive slotPositive z) j=nameRow z j
  rw [(source_unique (site L) positive slotPositive).extend_apply]

variable {F Tag : Type} [CommSemiring F] (scalar : Tag→List (List Bool)→F)
    (history : ∀v,Recipe Tag (Boundary N v)) (table : N.Tables F)
    (rep : Represents N scalar table history)

def recipes (i : Fin S) (v : Fin ((site L i).nodes)) :=
  DescentTerminalGraphRows.recipe N history p (node L i v) (L.operandRank _)

include rep in
theorem position_value (wp : 0<p) (i : Fin S) (v : Fin ((site L i).nodes)) (a : N.Assignment) (x : Ports bits) :
    (recipes L history i v).value (laneScalar (DescentTerminalGraphRows.clipScalar scalar)) (fun j=>
      let src := source (site L) positive slotPositive (sourceName (site L) ⟨i,v,j⟩)
      List.ofFn (payload L positive slotPositive payloadWidth a x src.1 src.2)) =
      N.read table a x (node L i v) := by
  subst p
  rw [←DescentTerminalGraphRows.recipe_read N scalar history wp table rep (node L i v) (L.operandRank _) a x]
  apply congrArg ((recipes L history i v).value (laneScalar (DescentTerminalGraphRows.clipScalar scalar)))
  funext j
  apply congrArg List.ofFn
  funext bit
  have location:=congrArg (fun nm:Names N (W*piece)=>readName (N:=N) a x nm bit) (catalog_arg L i v j)
  have value:=congrFun (read_name a x ((DescentTerminalGraphRows.number N (W*piece) (node L i v) (L.operandRank _)).symm j)) bit
  exact (payload_source L positive slotPositive rfl a x (sourceName (site L) ⟨i,v,j⟩) bit).trans (location.trans value)

include rep in
theorem graph_product (wp : 0<p) (a : N.Assignment) (x : Ports bits) :
    (∏i,∏v,(recipes L history i v).value (laneScalar (DescentTerminalGraphRows.clipScalar scalar)) (fun j=>
      let src := source (site L) positive slotPositive (sourceName (site L) ⟨i,v,j⟩)
      List.ofFn (payload L positive slotPositive payloadWidth a x src.1 src.2))) =
      ∏v,N.read table a x v := by
  calc
    _ = ∏i,∏v:Fin (Fintype.card (Nodes L i)),N.read table a x (node L i v) := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro v _
      exact position_value L positive slotPositive payloadWidth scalar history table rep wp i v a x
    _ = ∏i,∏v : Nodes L i,N.read table a x v.val := by
      apply Finset.prod_congr rfl
      intro i _
      exact (nodes L i).symm.prod_comp (fun v=>N.read table a x v.val)
    _ = _ := Fintype.prod_fiberwise _ _

end Order
end
end Hierarchy.DescentTerminalGraphPositions

end OAI
