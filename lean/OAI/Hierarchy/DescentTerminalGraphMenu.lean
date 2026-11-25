import OAI.Hierarchy.DescentTerminalGraphPositions

namespace OAI
/-! # Concrete scalar keys for physical terminal graph reads -/

namespace Hierarchy.DescentTerminalGraphMenu
open Computability.BorderVNP.Crossing DescentKernelHistory DescentTerminalGraphPositions DescentTerminalRecipeRows
open DescentTerminalRowBooks (Control)
open scoped Classical BigOperators
noncomputable section

abbrev ShortList (A M : ℕ) := (d : Fin (A+1)) × (Fin d.val→Fin (M+1))
def short (A M : ℕ) (xs : List ℕ) : ShortList A M :=
  ⟨⟨min A xs.length,Nat.lt_succ_of_le (min_le_left ..)⟩,fun j=>
    ⟨min M (xs.get ⟨j.val,j.isLt.trans_le (min_le_right ..)⟩),Nat.lt_succ_of_le (min_le_left ..)⟩⟩
def unshort {A M : ℕ} (b : ShortList A M) : List ℕ := List.ofFn (fun i=>(b.2 i).val)

def Fits (A M : ℕ) (xs : List ℕ) := xs.length ≤ A ∧ ∀n∈xs,n ≤ M

theorem unshort_short {A M : ℕ} {xs : List ℕ} (h : Fits A M xs) : unshort (short A M xs)=xs := by
  apply List.ext_getElem
  · simp [unshort,short,min_eq_right h.1]
  · intro i hi hi'
    have han := h.2 xs[i] (List.getElem_mem _)
    simp [unshort,short,min_eq_right han]

abbrev Tag (tags A U C : ℕ) := Fin tags × ShortList A U × ShortList A C
abbrev Count (tags A U C : ℕ) := Fintype.card (Tag tags A U C)
abbrev Raw (tags : ℕ) := (Fin tags × List ℕ) × List ℕ

def code (A U C : ℕ) {tags : ℕ} (r : Raw tags) : Fin (Count tags A U C) :=
  Fintype.equivFin _ (r.1.1,short A U r.1.2,short A C r.2)

def decode (tags A U C : ℕ) (k : Fin (Count tags A U C)) : Raw tags :=
  let v : Tag tags A U C := (Fintype.equivFin _).symm k
  ((v.1,unshort v.2.1),unshort v.2.2)
def FitsTag (A U C : ℕ) {tags : ℕ} (r : Raw tags) := Fits A U r.1.2 ∧ Fits A C r.2

theorem decode_code {tags A U C : ℕ} (r : Raw tags) (h : FitsTag A U C r) :
    decode tags A U C (code A U C r)=r := by
  simp [decode,code,unshort_short h.1,unshort_short h.2]

def numbered {B : Type} {tags : ℕ} (A U C : ℕ) (r : Recipe (Raw tags) B) :
    Recipe (Fin (Count tags A U C)) B := {r with tag := fun x=>code A U C (r.tag x)}

def dict {F : Type} {tags : ℕ} (A U C : ℕ) (old : Fin tags→List (List Bool)→F)
    (k : Fin (Count tags A U C)) : List (List Bool)→F :=
  laneScalar (DescentTerminalGraphRows.clipScalar old) (decode tags A U C k)

theorem numbered_value {F B : Type} [CommSemiring F] {tags A U C : ℕ}
    (r : Recipe (Raw tags) B) (old : Fin tags→List (List Bool)→F)
    (fit : ∀v,FitsTag A U C (r.tag v)) (x : B→List Bool) :
    (numbered A U C r).value (dict A U C old) x=
      r.value (laneScalar (DescentTerminalGraphRows.clipScalar old)) x := by
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro v _
  simp only [numbered,dict,decode_code _ (fit v)]

variable {D S p W q piece machineBits pool tags A U C H N0 A0 w V : ℕ}
    {P F : Type} [Fintype P] [CommSemiring F] {bits : P→ℕ} {G : Network D P bits}
    (order : Order G S p) (positive : 0<W) (slotPositive : 0<q) (payloadWidth : p=W*piece)
    (fit : ∀i,(order.site i).rows q ≤ W) (wordRoom : DescentTerminalBinReaddress.sliceWidth W q piece ≤ machineBits)
    (space : DescentTerminalBinPack.purchased W (counts (q:=q) order.site) ≤ pool)
    (history : ∀v,Recipe (Fin tags) (Boundary G v))
    (hH : ∀i v,Fintype.card (order.recipes history i v).Hidden ≤ H)
    (hN : ∀i v,Fintype.card (order.recipes history i v).Node ≤ N0)
    (hA : ∀i v j,(order.recipes history i v).arity j ≤ A0)
    (hw : ∀i v j,(order.recipes history i v).width j ≤ w)
    (hV : ∀i,(order.site i).nodes ≤ V)

abbrev Keys (q tags A U C H N0 A0 w V p : ℕ) :=
  DescentTerminalRowBooks.Keys q (Count tags A U C) H N0 A0 w V p

def menu (q A U C H N0 A0 w V p : ℕ) (old : Fin tags→List (List Bool)→F) :
    Fin (Keys q tags A U C H N0 A0 w V p)→F :=
  DescentTerminalRowBooks.menu q H N0 A0 w V p (dict A U C old)

def requests (A U C : ℕ) (a : G.Assignment) (outer : Ports bits) :
    Fin pool→Fin (Keys q tags A U C H N0 A0 w V (W*piece)) :=
  DescentTerminalRowBooks.request order.site positive slotPositive wordRoom
    (order.payload positive slotPositive payloadWidth a outer) space
    (fun i v=>numbered A U C (order.recipes history i v)) hH hN hA hw hV

include fit in
/-- No private or occurrence-specific scalar is stored in the request
array. Every row merely names a key in one finite shared menu. -/
theorem requests_graph_product (wp : 0<p) (small : ∀i v,(order.site i).arity v ≤ q)
    (localBounds : ∀i v atom,FitsTag A U C ((order.recipes history i v).tag atom))
    (old : Fin tags→List (List Bool)→F) (table : G.Tables F)
    (rep : Represents G old table history) (a : G.Assignment) (outer : Ports bits) :
    (∏u,menu q A U C H N0 A0 w V (W*piece) old
      (requests order positive slotPositive payloadWidth wordRoom space history hH hN hA hw hV A U C a outer u)) =
      ∏v,G.read table a outer v := by
  unfold requests menu
  have packed:=DescentTerminalRowBooks.requests_product order.site positive slotPositive fit wordRoom
    (order.payload positive slotPositive payloadWidth a outer) space
    (fun i v=>numbered A U C (order.recipes history i v)) hH hN hA hw hV small (dict A U C old)
  apply packed.trans
  refine Eq.trans ?_ (order.graph_product positive slotPositive payloadWidth old history table rep wp a outer)
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro v _
  exact numbered_value (order.recipes history i v) old (localBounds i v) _

end
end Hierarchy.DescentTerminalGraphMenu

end OAI
