import OAI.Hierarchy.DescentTerminalRecipeRows
import OAI.Hierarchy.DescentHistoryAdvice

namespace OAI
/-! # One shared scalar dictionary for bounded terminal row histories -/

namespace Hierarchy.DescentTerminalRowBooks
open DescentKernelHistory DescentTerminalRecipeRows Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section

/-- The short description stores operand addresses, tags and widths for
each actual atom. Cardinalities can vary from one occurrence to the next. -/
abbrev Book (q tags H N A w : ℕ) :=
  (h : Fin (H+1)) × (n : Fin (N+1)) × AddressBook q tags h.val n.val A w

/-- A table row contains the descriptions of just the occurrences it owns. -/
abbrev Control (q tags H N A w V : ℕ) :=
  (m : Fin (V+1)) × (Fin m.val → Book q tags H N A w)

variable {F : Type} [CommSemiring F] {q tags H N A w V p : ℕ}

def read (dict : Fin tags→List (List Bool)→F) (c : Control q tags H N A w V)
    (row : Fin q→Fin p→Bool) : F :=
  ∏ v,(c.2 v).2.2.read dict (fun col=>List.ofFn (row col))

variable {t : Site} (pos : 0<q) (history : (v : Fin t.nodes) → Recipe (Fin tags) (Fin (t.arity v)))
    (hidden : ∀v,Fintype.card (history v).Hidden ≤ H) (nodes : ∀v,Fintype.card (history v).Node ≤ N)
    (arity : ∀v i,(history v).arity i ≤ A) (width : ∀v i,(history v).width i ≤ w) (room : t.nodes ≤ V)

def book (v : Fin t.nodes) : Book q tags H N A w :=
  ⟨⟨_,Nat.lt_succ_of_le (hidden v)⟩,⟨_,Nat.lt_succ_of_le (nodes v)⟩,
    encode (history v) id (fun j=>(Site.target pos ⟨v,j⟩).2)
      (Fintype.equivFin _) (Fintype.equivFin _) (width v) (arity v)⟩

def control (r : Fin (t.rows q)) : Control q tags H N A w V :=
  let vs := {v : Fin t.nodes // Site.descriptor pos v=r}
  have card_le : Fintype.card vs ≤ t.nodes := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun v : Fin t.nodes => Site.descriptor pos v = r)
  ⟨⟨Fintype.card vs,Nat.lt_succ_of_le (card_le.trans room)⟩,
    fun i=>book pos history hidden nodes arity width (((Fintype.equivFin vs).symm i).val)⟩

theorem read_control (dict : Fin tags→List (List Bool)→F) (r : Fin (t.rows q))
    (row : Fin q→Fin p→Bool) :
    read dict (control pos history hidden nodes arity width room r) row =
      Site.rowScalar pos history dict r row := by
  let vs := {v : Fin t.nodes // Site.descriptor pos v=r}
  let f (v : vs) := (book pos history hidden nodes arity width v.val).2.2.read dict
    (fun col=>List.ofFn (row col))
  change (∏ i,f ((Fintype.equivFin vs).symm i))=_
  rw [(Fintype.equivFin vs).symm.prod_comp]
  apply Finset.prod_congr rfl
  intro v _
  exact encode_read (history v.val) id (fun j=>(Site.target pos ⟨v.val,j⟩).2)
    (Fintype.equivFin _) (Fintype.equivFin _) (width v.val) (arity v.val) dict
    (fun col=>List.ofFn (row col))

def controlBits (q tags H N A w V : ℕ) :=
  Nat.clog 2 (Fintype.card (Control q tags H N A w V))

def key (c : Control q tags H N A w V) (payload : Fin q→Fin p→Bool) :
    Tagged.Row (controlBits q tags H N A w V) × Tagged.Row (q*p) :=
  ((Fintype.equivFin _ c).castLE (Nat.le_pow_clog (by decide) _),
    (wordBits _).symm fun i=>payload (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

/-- A single scalar menu, independent of site, branch, and row. The
histogram service needs only the key, including when the field is infinite. -/
def scalar (q H N A w V p : ℕ) (dict : Fin tags→List (List Bool)→F)
    (k : Tagged.Row (controlBits q tags H N A w V) × Tagged.Row (q*p)) : F :=
  if h : k.1.val<Fintype.card (Control q tags H N A w V) then
    read dict ((Fintype.equivFin _).symm ⟨k.1.val,h⟩)
      (fun col j=>wordBits _ k.2 (finProdFinEquiv (col,j)))
  else 1

theorem scalar_key (dict : Fin tags→List (List Bool)→F) (c : Control q tags H N A w V)
    (row : Fin q→Fin p→Bool) :
    scalar q H N A w V p dict (key c row)=read dict c row := by
  let e := Fintype.equivFin (Control q tags H N A w V)
  have inside : (key c row).1.val < Fintype.card (Control q tags H N A w V) := (e c).isLt
  rw [scalar,dite_eq_left inside]
  change read dict (e.symm (e c)) _ = _
  simp only [Equiv.symm_apply_apply,key,Equiv.apply_symm_apply]

theorem scalar_control (dict : Fin tags→List (List Bool)→F) (r : Fin (t.rows q)) (row : Fin q→Fin p→Bool) :
    scalar q H N A w V p dict (key (control pos history hidden nodes arity width room r) row)=
      Site.rowScalar pos history dict r row := by
  rw [scalar_key,read_control]

theorem shared_size {bits : ℕ} (fits : controlBits q tags H N A w V+q*p ≤ bits/2) :
    Fintype.card (Tagged.Row (controlBits q tags H N A w V) × Tagged.Row (q*p)) ≤ 2^(bits/2) := by
  simp only [Tagged.Row,Fintype.card_prod,Fintype.card_fin,←pow_add]
  exact Nat.pow_le_pow_right (by decide) fits

section Position
open DescentTerminalBinReaddress
variable {sitesCount W machineBits piece : ℕ} (sites : Fin sitesCount→Site)
    (positive : 0<W) (slotPositive : 0<q) (fit : ∀i,(sites i).rows q ≤ W)
    (wordRoom : sliceWidth W q piece ≤ machineBits)
    (pay : Fin (Bins (W:=W) (q:=q) sites)→Payload W q piece)

def rowData (i : Fin sitesCount) (r : Fin ((sites i).rows q)) (col : Fin q) : Fin (W*piece)→Bool :=
  let t := global sites positive ⟨i,r,col⟩
  DescentTerminalBinReaddress.read wordRoom (fun u=>entry machineBits piece (DescentTerminalBinFormat.address W q)
    (DescentTerminalRecipeRows.control sites positive slotPositive t.1) (gather (pay t.1) u)) t.2

include fit in
/-- Multiplying the keys of a position's physical table rows evaluates
the original occurrence histories at the matching physical port words. -/
theorem position_product (i : Fin sitesCount) (small : ∀v,(sites i).arity v ≤ q)
    (recipes : (v : Fin (sites i).nodes)→Recipe (Fin tags) (Fin ((sites i).arity v)))
    (hH : ∀v,Fintype.card (recipes v).Hidden ≤ H) (hN : ∀v,Fintype.card (recipes v).Node ≤ N)
    (hA : ∀v j,(recipes v).arity j ≤ A) (hw : ∀v j,(recipes v).width j ≤ w)
    (hV : (sites i).nodes ≤ V) (dict : Fin tags→List (List Bool)→F) :
    (∏r,scalar q H N A w V (W*piece) dict (key (control slotPositive recipes hH hN hA hw hV r)
       (rowData sites positive slotPositive wordRoom pay i r))) =
      ∏v,(recipes v).value dict (fun j=>
        let src := source sites positive slotPositive (sourceName sites ⟨i,v,j⟩)
        List.ofFn (pay src.1 src.2)) := by
  simp_rw [scalar_control]
  rw [Site.scalar_product slotPositive small]
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  apply congrArg List.ofFn
  funext k
  exact reassembled_arg sites positive slotPositive wordRoom fit pay ⟨i,v,j⟩ k

abbrev LocalRow := (i : Fin sitesCount) × Fin ((sites i).rows q)
def rows : List (LocalRow (q:=q) sites) :=
  (List.finRange sitesCount).flatMap fun i=>List.ofFn (fun r=>⟨i,r⟩)

theorem mem_rows (a : LocalRow (q:=q) sites) : a∈rows sites :=
  List.mem_flatMap.mpr ⟨a.1,List.mem_finRange _,List.mem_ofFn.mpr ⟨a.2,rfl⟩⟩

def padded {A X : Type} {M : ℕ} (idx : A ↪ Fin M) (f : A→X)
    (ls : List A) (defaultValue : X) (i : Fin M) : X :=
  ((scatter idx f ls)[i.val]'i.isLt).getD defaultValue

theorem padded_live {A X : Type} {M : ℕ} (idx : A ↪ Fin M) (f : A → X) (ls : List A)
    (empty : X) (a : A) (h : a ∈ ls) : padded idx f ls empty (idx a) = f a :=
  congrArg (fun entry : Option X => entry.getD empty) (scatter_live (W:=M) (q:=1) idx f idx.injective ls h)

theorem padded_empty {A X : Type} {M : ℕ} (idx : A ↪ Fin M) (f : A → X) (ls : List A)
    (empty : X) (i : Fin M) (h : ∀ a ∈ ls, idx a ≠ i) : padded idx f ls empty i = empty :=
  congrArg (fun entry : Option X => entry.getD empty) (scatter_empty (W:=M) (q:=1) idx f ls i h)

theorem prod_padded {A X : Type} [Fintype A] {M : ℕ}
    (idx : A ↪ Fin M) (f : A→X) (ls : List A) (all : ∀a,a∈ls) (empty : X)
    (weight : X→F) (unit : weight empty=1) :
    (∏i,weight (padded idx f ls empty i))=∏a,weight (f a) := by
  let read := fun i=>weight (padded idx f ls empty i)
  have live (a : A) : read (idx a)=weight (f a) := by
    exact congrArg weight (padded_live idx f ls empty a (all a))
  have gap (i : Fin M) (missing : i∉Finset.univ.image idx) : read i=1 := by
    have h (a : A) (_ : a∈ls) : idx a≠i := fun eqn=>missing (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,eqn⟩)
    exact (congrArg weight (padded_empty idx f ls empty i h)).trans unit
  calc
    _ = ∏ i ∈ Finset.univ.image idx,read i := (Finset.prod_subset (Finset.subset_univ _) (fun i _ h=>gap i h)).symm
    _ = ∏ a : A,read (idx a) := Finset.prod_image idx.injective.injOn
    _ = _ := Finset.prod_congr rfl fun a _=>live a

abbrev Keys (q tags H N A w V p : ℕ) := 2^(controlBits q tags H N A w V)*2^(q*p)

def menu (q H N A w V p : ℕ) (dict : Fin tags→List (List Bool)→F)
    (k : Fin (Keys q tags H N A w V p)) : F :=
  scalar q H N A w V p dict (finProdFinEquiv.symm k)

def emptyKey (q tags H N A w V p : ℕ) : Fin (Keys q tags H N A w V p) :=
  finProdFinEquiv (key (p:=p) (⟨⟨0,Nat.zero_lt_succ V⟩,Fin.elim0⟩ : Control q tags H N A w V) (fun _ _=>false))

private theorem empty_key_unit (q H N A w V p : ℕ) (dict : Fin tags→List (List Bool)→F) :
    menu q H N A w V p dict (emptyKey q tags H N A w V p)=1 := by
  unfold menu emptyKey
  rw [Equiv.symm_apply_apply,scalar_key]
  exact Finset.prod_of_isEmpty _

variable {pool : ℕ} (space : DescentTerminalBinPack.purchased W (counts (q:=q) sites) ≤ pool)
    (recipes : (i : Fin sitesCount)→(v : Fin (sites i).nodes)→Recipe (Fin tags) (Fin ((sites i).arity v)))
    (hH : ∀i v,Fintype.card (recipes i v).Hidden ≤ H) (hN : ∀i v,Fintype.card (recipes i v).Node ≤ N)
    (hA : ∀i v j,(recipes i v).arity j ≤ A) (hw : ∀i v j,(recipes i v).width j ≤ w)
    (hV : ∀i,(sites i).nodes ≤ V)

def rowAddress : LocalRow (q:=q) sites ↪ Fin pool :=
  (DescentTerminalBinPack.rowIndex positive (counts (q:=q) sites)).trans (Fin.castLEEmb space)

def localKey (a : LocalRow (q:=q) sites) : Fin (Keys q tags H N A w V (W*piece)) :=
  finProdFinEquiv (key (control slotPositive (recipes a.1) (hH a.1) (hN a.1) (hA a.1) (hw a.1) (hV a.1) a.2)
    (rowData sites positive slotPositive wordRoom pay a.1 a.2))

/-- The histogram sees exactly one small integer key for every row of a
common purchased pool. The unused rows use the same empty key in every
branch. The range injection uses the actual site's prefix allocation. -/
def request (u : Fin pool) : Fin (Keys q tags H N A w V (W*piece)) :=
  padded (rowAddress sites positive space)
    (localKey sites positive slotPositive wordRoom pay recipes hH hN hA hw hV)
    (rows sites) (emptyKey q tags H N A w V (W*piece)) u

theorem request_at (a : LocalRow (q:=q) sites) :
    request sites positive slotPositive wordRoom pay space recipes hH hN hA hw hV (rowAddress sites positive space a)=
      localKey sites positive slotPositive wordRoom pay recipes hH hN hA hw hV a := by
  exact padded_live _ _ _ _ a (mem_rows sites a)

theorem request_gap (u : Fin pool) (gap : ∀a,rowAddress sites positive space a≠u) :
    request sites positive slotPositive wordRoom pay space recipes hH hN hA hw hV u=
      emptyKey q tags H N A w V (W*piece) := by
  exact padded_empty _ _ _ _ u (fun a _ => gap a)

include fit in
theorem requests_product (small : ∀i v,(sites i).arity v ≤ q) (dict : Fin tags→List (List Bool)→F) :
    (∏u,menu q H N A w V (W*piece) dict
      (request sites positive slotPositive wordRoom pay space recipes hH hN hA hw hV u)) =
    ∏i,∏v,(recipes i v).value dict (fun j=>
      let src := source sites positive slotPositive (sourceName sites ⟨i,v,j⟩)
      List.ofFn (pay src.1 src.2)) := by
  unfold request
  rw [prod_padded _ _ _ (mem_rows sites) _ _ (empty_key_unit ..),Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [menu,localKey,Equiv.symm_apply_apply] using
    position_product sites positive slotPositive fit wordRoom pay i (small i) (recipes i)
      (hH i) (hN i) (hA i) (hw i) (hV i) dict

end Position

end
end Hierarchy.DescentTerminalRowBooks

end OAI
