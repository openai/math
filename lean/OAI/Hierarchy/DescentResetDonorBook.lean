import OAI.Hierarchy.DescentContactDonorCargo

namespace OAI
/-! # One catalog of contact lookups for all reset blocks -/
namespace Hierarchy.DescentResetDonorBook
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM DescentContactDonorSelection
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q a b M H G w n : ℕ}

def width (a b M : ℕ):=max (dictBits a b M) (DescentFirstContactPayload.pageBits b M)
def words (q a b M : ℕ):=(q+1)*2*2^(width a b M)
def page (req : Fin q→ℕ) (a b M : ℕ) (j : Fin ((q+1)*2)) : Page:=
  let p : Fin (q+1)×Fin 2:=finProdFinEquiv.symm j
  Fin.cases (motive := fun _ => Page) (DescentFirstContactPayload.pages b M p.2)
    (fun t => DescentContactDonorSelection.pages (req t) a b M p.2) p.1
def ix (t : Fin (q+1)) (j : Fin 2) : Fin ((q+1)*2):=finProdFinEquiv (t,j)
def table (req : Fin q→ℕ) (a b M base : ℕ) (t : Fin (q+1)):=joined (page req a b M) (width a b M) base (ix t)

theorem prefer_page (req : Fin q→ℕ) (a b M : ℕ) (j : Fin 2) :
    page req a b M (ix 0 j)=DescentFirstContactPayload.pages b M j:=by simp [page,ix]
theorem request_page (req : Fin q→ℕ) (a b M : ℕ) (t : Fin q) (j : Fin 2) :
    page req a b M (ix t.succ j)=DescentContactDonorSelection.pages (req t) a b M j:=by simp [page,ix]
theorem size (req : Fin q→ℕ) (a b M : ℕ) (t : Fin ((q+1)*2)) : (page req a b M t).bits≤width a b M:=by
  obtain ⟨⟨i,j⟩,rfl⟩:=finProdFinEquiv.surjective t
  induction i using Fin.cases with
  | zero=>
    change (page req a b M (ix 0 j)).bits≤_
    rw [prefer_page]
    exact (DescentFirstContactPayload.page_room b M j).trans (Nat.le_max_right ..)
  | succ i=>
    change (page req a b M (ix i.succ j)).bits≤_
    rw [request_page]
    exact (DescentContactDonorSelection.page_fits (req i) a b M j).trans (Nat.le_max_left ..)

def expression (req : Fin q→ℕ) (a b M base : ℕ) (t : Fin q) (own cargo : Fin n→Expr) :=
  let take:=table req a b M base t.succ
  DescentFirstContactPayload.exprOn (table req a b M base 0) (fun j=>take.read (own j) (cargo j)) (List.finRange n)

theorem installed (req : Fin q→ℕ) (a b M base : ℕ) (m : Memory w) (room : base+words q a b M<2^w) :
    let P:=page req a b M
    let width_:=width a b M
    let dst:=after P width_ base m
    (mount P width_ w base).Exec m dst (4+10*words q a b M) ∧
      Static (table req a b M base 0) (DescentFirstContactPayload.prefer (b:=b)) M dst ∧
      (∀t,Static (table req a b M base t.succ) (keep (a:=a) (b:=b) (req t)) M dst) ∧
      (∀i,i<base ∨ base+words q a b M≤ i→dst i=m i) ∧ CheapCode (mount P width_ w base) ∧
      DescentStaticWordColumn.names (mount P width_ w base)=15*(words q a b M+1):=by
  intro P width_ dst
  obtain ⟨exec,names⟩:=DescentOrdinaryAtomFieldRAM.ROM.run P width_ base m room
  exact ⟨exec,
    binary_mounted _ M P width_ base m (size req a b M) (ix 0) (prefer_page req a b M),
    fun t=>binary_mounted _ M P width_ base m (size req a b M) (ix t.succ) (request_page req a b M t),
    frame P width_ base m,cheap P width_ w base,names⟩

theorem price (req : Fin q→ℕ) (a b M base : ℕ) (t : Fin q) (own cargo : Fin n→Expr) (cost : ℕ)
    (bounded : ∀i,(own i).work+(cargo i).work≤cost) :
    (expression req a b M base t own cargo).work≤1+n*(cost+22):=by
  let mask:=table req a b M base t.succ
  let fold:=table req a b M base 0
  let term:=fun i=>mask.read (own i) (cargo i)
  have on (l : List (Fin n)) : (DescentFirstContactPayload.exprOn fold term l).work≤1+l.length*(cost+22):=by
    induction l with
    | nil=>simp [DescentFirstContactPayload.exprOn,Expr.work]
    | cons i tail ih=>
      have hi:=bounded i
      have termWork : (term i).work = (own i).work + (cargo i).work + 11 :=
        DescentPackedZip.work mask (own i) (cargo i)
      rw [DescentFirstContactPayload.exprOn,DescentPackedZip.work,termWork,List.length_cons,Nat.succ_mul]
      omega
  simpa [expression,mask,fold,term] using on (List.finRange n)

theorem fit (req : Fin q→ℕ) (a b M base out : ℕ) (j : Fin q) (own cargo : Fin n→Expr)
    (bounds : ∀i,(own i).Fits w base ∧ (cargo i).Fits w base)
    (belowOut : base+words q a b M≤out) (small : out<2^w) :
    (expression req a b M base j own cargo).Fits w out:=by
  let P:=page req a b M
  have held (i : Fin (q+1)) (k : Fin 2) : (bank P (width a b M) base (ix i k)).Fits w out:=
    bank_room P _ base out _ (size req a b M _) belowOut small
  have early : base ≤ out := (Nat.le_add_right base (words q a b M)).trans belowOut
  apply DescentContactDonorCargo.fold_fits (table req a b M base 0)
    (fun i => (table req a b M base j.succ).read (own i) (cargo i))
    (List.finRange n) out w (held 0 0) (held 0 1)
  intro i
  have low:=ProtocolRAMGeneratedWrite.fits_mono (own i) early (bounds i).1
  have high:=ProtocolRAMGeneratedWrite.fits_mono (cargo i) early (bounds i).2
  exact ⟨held j.succ 1,high,held j.succ 0,low⟩

theorem read (req : Fin q→ℕ) (base out : ℕ) (m : Memory w) (j : Fin q) (own cargo : Fin n→Expr)
    (labels : Fin n→Fin H→Fin G→Cell a) (contents : Fin n→Fin H→Fin G→Cell b)
    (bounds : ∀i,(own i).Fits w base ∧ (cargo i).Fits w base)
    (inputs : ∀i,Source (own i) (labels i) M m ∧ Source (cargo i) (contents i) M m)
    (belowOut : base+words q a b M≤out) (small : out<2^w) :
    let e:=expression req a b M base j own cargo
    let dst:=after (page req a b M) (width a b M) base m
    e.Fits w out ∧ Source e (fun h g=>visits (req j) (fun i=>labels i h g) (fun i=>contents i h g)) M dst:=by
  intro e dst
  let P:=page req a b M
  let bits:=width a b M
  have early : base≤out:=(Nat.le_add_right base (words q a b M)).trans belowOut
  obtain ⟨_,firstBy,matchBy,ret,_,_⟩:=installed req a b M base m (belowOut.trans_lt small)
  have held (i : Fin (q+1)) (k : Fin 2) : (bank P bits base (ix i k)).Fits w out:=
    bank_room P bits base out _ (size req a b M _) belowOut small
  have cap (k : Fin 2) : (P (ix j.succ k)).bits=(DescentContactDonorSelection.pages (req j) a b M k).bits:=
    congrArg Page.bits (request_page req a b M j k)
  have first (k : Fin 2) : (P (ix 0 k)).bits=(DescentFirstContactPayload.pages b M k).bits:=
    congrArg Page.bits (prefer_page req a b M k)
  have keepSource {c : ℕ} (p : Expr) (v : Fin H→Fin G→Cell c) (fit : p.Fits w base) (got : Source p v M m) : Source p v M dst:=
    fun row=>(ProtocolRAM.eval_below p _ m dst fit (fun addr lt=>ret addr (.inl lt))).trans (got row)
  apply DescentContactDonorCargo.fold_source (table req a b M base j.succ) (table req a b M base 0) (req j) own cargo out dst labels contents
  · intro i
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ early (bounds i).1,ProtocolRAMGeneratedWrite.fits_mono _ early (bounds i).2,
      held j.succ 0,held j.succ 1,cap 0,cap 1⟩
  · intro i;exact ⟨keepSource _ _ (bounds i).1 (inputs i).1,keepSource _ _ (bounds i).2 (inputs i).2⟩
  · exact matchBy j
  · exact held 0 0
  · exact held 0 1
  · exact first 0
  · exact first 1
  · exact firstBy

end
end Hierarchy.DescentResetDonorBook

end OAI
