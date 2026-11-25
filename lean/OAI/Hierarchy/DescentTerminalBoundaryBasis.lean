import OAI.Hierarchy.DescentTerminalGraphVolume
import OAI.Hierarchy.DescentBundleHistory
import OAI.Hierarchy.DescentBitDescription

namespace OAI
/-! # Terminal local scalar on one input slot per actual incident bundle

The boundary file is fixed by the terminal graph. Repeated reads of a surviving
bundle refer to the same row coordinate in the retained scalar descriptor.
The final short chunk of a wire remains an ordinary zero-padded input. -/
namespace Hierarchy.DescentTerminalBoundaryBasis
open Computability.BorderVNP.Crossing DescentKernelHistory DescentBundleHistory DescentTerminalGraphPositions
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
variable {D p tags : ℕ} {F Tag P : Type} [CommSemiring F] [Fintype P] {bits:P→ℕ}
    (G:Network D P bits)
abbrev SiteRef (v : G.Site) := BlockRef p (boundaryWidth G v)

def part (hp : 0<p) {v : G.Site} (b : SiteRef (p:=p) G v) : DescentTerminalGraphRows.Part G p v :=
  ⟨b.port,⟨b.block,by
    have cover:=CallPool.count_le_batches_mul (boundaryWidth G v b.port) p hp
    rw [Nat.mul_comm p] at cover
    exact Nat.le_of_mul_le_mul_right (b.fits.trans cover) hp⟩⟩

omit [Fintype P] in
theorem read_part (hp : 0<p) {v : G.Site} (b : SiteRef (p:=p) G v) (a : G.Assignment) (x : Ports bits) :
    Order.readName (N:=G) a x (name G (part G hp b))=fun d=>bitInput G a x v (b.atBit d) := by
  funext d
  rcases b with ⟨port,k,room⟩
  have bound : k*p+d.val<boundaryWidth G v port := (Nat.add_lt_add_left d.isLt _).trans_le (by simpa [Nat.succ_mul] using room)
  cases port with
  | inl e=>simpa [Order.readName,name,part,TaggedShorterFields.slice,bitInput,boundaryRead,BlockRef.atBit,bound,boundaryWidth] using
      (show (if h : k*p+d.val<G.width e.val then a e.val ⟨_,h⟩ else false)=_ from dite_eq_left bound)
  | inr z=>simpa [Order.readName,name,part,TaggedShorterFields.slice,bitInput,boundaryRead,BlockRef.atBit,bound,boundaryWidth] using
      (show (if h : k*p+d.val<bits z.val then x z.val ⟨_,h⟩ else false)=_ from dite_eq_left bound)

def address (hp:0<p) {v:G.Site} (rank:Boundary G v↪ℕ) (b:SiteRef (p:=p) G v) :
    Fin (DescentTerminalGraphRows.arity G p v) :=
  DescentTerminalGraphRows.number G p v rank (part G hp b)

theorem address_val (hp:0<p) {v:G.Site} (rank:Boundary G v↪ℕ) (b:SiteRef (p:=p) G v) :
    (address G hp rank b).val=ProtocolRAMPortRanks.«prefix» (fun d=>poolBatchCount (boundaryWidth G v d) p) rank b.port+b.block := rfl

theorem address_injective (hp:0<p) {v:G.Site} (rank:Boundary G v↪ℕ) : Function.Injective (address G hp rank) := by
  intro a b h
  have he:part G hp a=part G hp b:=(DescentTerminalGraphRows.number G p v rank).injective h
  have field:a.port=b.port:=congrArg Sigma.fst he
  have chunk:a.block=b.block:=congrArg (fun pos:DescentTerminalGraphRows.Part G p v=>pos.2.val) he
  cases a;cases b;simp_all

theorem source_word (hp:0<p) {v:G.Site} (rank:Boundary G v↪ℕ) (b:SiteRef (p:=p) G v)
    (a:G.Assignment) (x:Ports bits) :
    Order.readName (N:=G) a x (name G ((DescentTerminalGraphRows.number G p v rank).symm (address G hp rank b))) =
      fun d=>bitInput G a x v (b.atBit d) := by
  simpa [address] using read_part G hp b a x

def numbered (hp:0<p) (v:G.Site) (rank:Boundary G v↪ℕ)
    (r:Recipe Tag (SiteRef (p:=p) G v)) (code:Tag→Fin tags) :
    Recipe (Fin tags) (Fin (DescentTerminalGraphRows.arity G p v)) where
  Hidden:=r.Hidden
  width:=r.width
  Node:=r.Node
  tag:=code ∘ r.tag
  arity:=r.arity
  operand u j:=(r.operand u j).map (address G hp rank) id

theorem valued (hp:0<p) (v:G.Site) (rank:Boundary G v↪ℕ) (r:Recipe Tag (SiteRef (p:=p) G v))
    (code:Tag→Fin tags) (dict:Fin tags→List (List Bool)→F) (scalar:Tag→List (List Bool)→F)
    (tagRead:∀u xs,dict (code (r.tag u)) xs=scalar (r.tag u) xs)
    (words:Fin (DescentTerminalGraphRows.arity G p v)→List Bool) :
    (numbered G hp v rank r code).value dict words=r.value scalar (words ∘ address G hp rank) := by
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro u _
  change dict (code (r.tag u)) _=_
  rw [tagRead u]
  congr 2
  funext j
  cases hh:r.operand u j <;> simp [numbered,hh]

theorem graph_value (hp:0<p) (v:G.Site) (rank:Boundary G v↪ℕ) (r:Recipe Tag (SiteRef (p:=p) G v))
    (code:Tag→Fin tags) (dict:Fin tags→List (List Bool)→F) (scalar:Tag→List (List Bool)→F)
    (tagRead:∀u xs,dict (code (r.tag u)) xs=scalar (r.tag u) xs) (a:G.Assignment) (x:Ports bits) :
    (numbered G hp v rank r code).value dict (fun t=>wordList (Order.readName (N:=G) a x
      (name G ((DescentTerminalGraphRows.number G p v rank).symm t))))=
      r.value scalar (fun b=>wordList (fun d=>bitInput G a x v (b.atBit d))) := by
  rw [valued G hp v rank r code dict scalar tagRead]
  congr 1
  funext b
  exact congrArg wordList (source_word G hp rank b a x)

theorem numbered_value (hp:0<p) (v:G.Site) (rank:Boundary G v↪ℕ) (r:Recipe Tag (SiteRef (p:=p) G v))
    (code:Tag→Fin tags) (dict:Fin tags→List (List Bool)→F) (scalar:Tag→List (List Bool)→F)
    (tagRead:∀u xs,dict (code (r.tag u)) xs=scalar (r.tag u) xs) (a:G.Assignment) (x:Ports bits) :
    (numbered G hp v rank r code).value dict (fun j=>wordList (DescentTerminalGraphRows.readPart G p a x
      ((DescentTerminalGraphRows.number G p v rank).symm j)))=
      r.value scalar (fun b=>wordList (fun d=>bitInput G a x v (b.atBit d))) := by
  simpa only [Order.read_name] using graph_value G hp v rank r code dict scalar tagRead a x

end
end Hierarchy.DescentTerminalBoundaryBasis

end OAI
