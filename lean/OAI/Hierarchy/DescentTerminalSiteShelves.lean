import OAI.Hierarchy.DescentTerminalChronologicalBooks

namespace OAI
/-! # Paid row selections from the ordered little-endian book of an entire terminal site -/
namespace Hierarchy.DescentTerminalSiteShelves
open DescentKernelHistory DescentTerminalRowBooks DescentTerminalRecipeRows DescentTerminalScalarHeader
open DescentTerminalChronologicalBooks DescentTerminalBinPack Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V : ℕ}
local notation "B" => Book q t H N A w
local notation "C" => Control q t H N A w V

/-- A single graph vertex has an arity plus its numerical local scalar book. All its
public slots are initially vertex-local. Its private slots use their original restricted order. -/
abbrev Row := Fin (q+1) × B
abbrev Home := (v : Fin (V+1)) × (Fin v.val→Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w))

def rowRange (q t H N A w : ℕ) := (q+1)*bookRange q t H N A w
def recordBits (q tagBits H N A w : ℕ) :=
  Nat.clog 2 (q+1)+DescentTerminalControlBits.bookBits q tagBits H N A w

theorem record_room (tagBits : ℕ) (tagsFit : t≤2^tagBits) :
    rowRange q t H N A w≤2^(recordBits q tagBits H N A w) := by
  unfold rowRange recordBits
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (book_range_room q t H N A w tagBits tagsFit)

def range (q t H N A w V : ℕ) := (V+1)*(rowRange q t H N A w)^V
def storeRow (r : Row (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (q:=q)) : Fin (rowRange q t H N A w) :=
  finProdFinEquiv (r.1,DescentTerminalScalarHeader.book r.2)
def loadRow (i : Fin (rowRange q t H N A w)) : Row (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (q:=q) :=
  let z:Fin (q+1)×Fin (bookRange q t H N A w):=finProdFinEquiv.symm i
  (z.1,readBook z.2)
theorem row_back (r : Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)) : loadRow (storeRow r)=r := by
  cases r;simp [storeRow,loadRow,book_back]

def store (z : Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)) : Fin (range q t H N A w V) :=
  finProdFinEquiv (z.1,finFunctionFinEquiv (extend (fun i=>storeRow (z.2 i)) (storeRow (0,emptyBook q t H N A w)) :
    Fin V→Fin (rowRange q t H N A w)))

def load (i : Fin (range q t H N A w V)) : Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) :=
  let z:Fin (V+1)×Fin ((rowRange q t H N A w)^V):=finProdFinEquiv.symm i
  ⟨z.1,fun v=>loadRow ((finFunctionFinEquiv.symm z.2) (v.castLE (Nat.le_of_lt_succ z.1.isLt)))⟩

theorem load_store (z : Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)) : load (store z)=z := by
  rcases z with ⟨n,rows⟩
  let packed : Fin ((rowRange q t H N A w)^V) := finFunctionFinEquiv
    (extend (fun i => storeRow (rows i)) (storeRow (0,emptyBook q t H N A w)))
  let unpack (p : Fin (V+1) × Fin ((rowRange q t H N A w)^V)) :
      Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) :=
    ⟨p.1,fun i => loadRow (finFunctionFinEquiv.symm p.2 (i.castLE (Nat.le_of_lt_succ p.1.isLt)))⟩
  change unpack (finProdFinEquiv.symm (finProdFinEquiv (n,packed))) = _
  rw [Equiv.symm_apply_apply]
  simp only [unpack,packed,Equiv.symm_apply_apply,extend_castLE,row_back]

/-- Readdress only the public half. The hidden ordinal belongs to this vertex's book. -/
def move (f : Fin q→Fin q) (b : B) : B :=
  ⟨b.1,b.2.1,⟨b.2.2.width,fun i=>(b.2.2.rows i).map fun it=>(it.1,it.2.1,fun k=>(it.2.2 k).map (Sum.map f id))⟩⟩

def shift {s : ℕ} (a : Fin s→ℕ) (qp : 0<q) (v : Fin s) (j : Fin q) : Fin q :=
  ⟨(first q a v+j.val)%q,Nat.mod_lt _ qp⟩

def place {s : ℕ} (a : Fin s→ℕ) (_qp : 0<q) (v : Fin s) :=
  if 0<a v then (first q a v)/q else bins q a

theorem target_slot (site : Site) (qp : 0<q) (v : Fin site.nodes) (j : Fin (site.arity v))
    (small : site.arity v≤q) : (Site.target qp ⟨v,j⟩).2=shift site.arity qp v (j.castLE small) := by
  apply Fin.ext
  rfl

theorem descriptor_row (site : Site) (qp : 0<q) (v : Fin site.nodes) :
    (site.descriptor qp v).val=site.portRows q+place site.arity qp v := by
  by_cases live : 0<site.arity v
  · simp only [Site.descriptor,dite_eq_left live,place,ite_eq_left live]
    change site.portRows q+(first q site.arity v+0)/q=_
    simp
  · simp [Site.descriptor,live,place,Site.tableRows]

def selectRow (z : Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)) (qp : 0<q)
    (ports localRow : ℕ) : C :=
  let a:=fun v=>(z.2 v).1.val
  select (fun v=>ports+place a qp v=localRow) (Nat.le_of_lt_succ z.1.isLt) (fun v=>move (shift a qp v) (z.2 v).2)

section Actual
variable (site : Site) (qp : 0<q) (recipes : ∀v : Fin site.nodes,Recipe (Fin t) (Fin (site.arity v)))
    (birth : Birth recipes) (hH : ∀v,Fintype.card (recipes v).Hidden≤H) (hN : ∀v,Fintype.card (recipes v).Node≤N)
    (hA : ∀v j,(recipes v).arity j≤A) (hw : ∀v j,(recipes v).width j≤w)
    (sitesFit : site.nodes≤V) (short : ∀v,site.arity v≤q)

def localBook (v : Fin site.nodes) : B :=
  ⟨⟨_,Nat.lt_succ_of_le (hH v)⟩,⟨_,Nat.lt_succ_of_le (hN v)⟩,
    DescentKernelHistory.encode (recipes v) id (Fin.castLE (short v)) (ordinal (birth.hidden v)) (ordinal (birth.atom v)) (hw v) (hA v)⟩

def actual : Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) :=
  ⟨⟨site.nodes,Nat.lt_succ_of_le sitesFit⟩,fun v=>(⟨site.arity v,Nat.lt_succ_of_le (short v)⟩,
    localBook site recipes birth hH hN hA hw short v)⟩

theorem moved (v : Fin site.nodes) : move (shift site.arity qp v) (localBook site recipes birth hH hN hA hw short v)=
    DescentTerminalChronologicalBooks.book qp recipes birth hH hN hA hw v := by
  have mapped {β γ : Type} (hidden : β → γ) (z : Fin (site.arity v) ⊕ β) :
      Sum.map (shift site.arity qp v) id (Sum.map (Fin.castLE (short v)) hidden z) =
        Sum.map (fun j => (Site.target (t:=site) qp ⟨v,j⟩).2) hidden z := by
    cases z with
    | inl j => exact congrArg Sum.inl (target_slot site qp v j (short v)).symm
    | inr _ => rfl
  unfold move localBook DescentTerminalChronologicalBooks.book
  congr 3
  funext i
  simp only [DescentKernelHistory.encode,Option.map_some]
  congr 3
  funext j
  split <;> rename_i bound <;> simp [mapped]

theorem selected (r : Fin (site.rows q)) :
    selectRow (load (store (actual site recipes birth hH hN hA hw sitesFit short))) qp (site.portRows q) r.val=
      DescentTerminalChronologicalBooks.control qp recipes birth hH hN hA hw sitesFit r := by
  rw [load_store]
  unfold selectRow actual DescentTerminalChronologicalBooks.control
  dsimp only
  have owns : (fun v : Fin site.nodes=>site.portRows q+place site.arity qp v=r.val)=
      (fun v=>site.descriptor qp v=r) := by
    funext v
    rw [Fin.ext_iff,descriptor_row site qp v]
  rw [owns]
  congr 1
  funext v
  exact moved site qp recipes birth hH hN hA hw short v

end Actual
end
end Hierarchy.DescentTerminalSiteShelves

end OAI
