import OAI.Hierarchy.DescentPackedScalarDonorOperands

namespace OAI
/-! # The scalar population in every occupied or padded previous donor book -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a b K D r H G M w : ℕ}

def support (x : Cell (a*K)) :=Finset.univ.filter (fun j : Fin K=>(encode a K).symm x j≠0)
def count (b : ℕ) (x : Cell (a*K)) : Cell b :=(support x).card

theorem empty : count (a:=a) (K:=K) b 0=0 :=by
  have z:encode a K (fun _=>0)=0:=by apply Fin.ext;change (finFunctionFinEquiv (fun _ : Fin K=>(0:Cell a))).val=0;simp []
  have e: (encode a K).symm 0=(fun _=>0):=(encode a K).symm_apply_eq.mpr z.symm
  simp [count,support,e]

theorem exact_count {X : Type} [Fintype X] (ids : X↪Fin K) (x : Cell (a*K))
    (bits : ∀j,(encode a K).symm x j≠0 ↔ ∃u,ids u=j) (room : K<2^b) : (count b x).val=Fintype.card X :=by
  have s : support x=Finset.univ.map ids:=by ext j;simp [support,bits]
  have card : (support x).card=Fintype.card X:=by rw [s,Finset.card_map,Finset.card_univ]
  change ((support x).card:Cell b).val=_
  rw [Fin.val_cast_of_lt ((support x).card_le_univ.trans_lt (by simpa using room)),card]

def page (a K b M : ℕ) : ROM.Page :=⟨(a*K)*M,fun i=>(DescentSIMDLookup.table (M:=M) (count (a:=a) (K:=K) b) i).val⟩

def value (walks : Fin H→Fin D→Option (Fin H)) (prev : Fin r→Fin H→Fin G→Cell (a*K)) (b : ℕ)
    (h : Fin H) (g : Fin G) (i : Fin (D*r)) :=
  let z:=finProdFinEquiv.symm i
  (DescentSortedRoster.indexed walks h z.1).elim 0 (fun v=>count b (prev z.2 v g))

def expr (P : Ports D) (old : Fin r→Bank) (dictionary : Bank) (H : ℕ) (i : Fin (D*r)) : Expr:=
  let z:=finProdFinEquiv.symm i
  .lookup dictionary (peerExpr P (old z.2) H z.1)

private theorem count_peer {V : Type} (peer : Option V) (word : V→Cell (a*K)) :
    count (a:=a) (K:=K) b (peer.elim 0 word) =
      peer.elim 0 (fun v=>count (a:=a) (K:=K) b (word v)) := by
  cases peer with
  | none=>exact empty
  | some _=>rfl

theorem source (P : Ports D) (old : Fin r→Bank) (dict : Bank) (base : ℕ) (m : Memory w)
    (walks : Fin H→Fin D→Option (Fin H)) (prev : Fin r→Fin H→Fin G→Cell (a*K))
    (mounted : Mounted P (DescentSortedRoster.indexed walks) m G M) (stored : ∀x,Reads (old x) (prev x) M m)
    (access : ∀x,Accessible P (old x) H G M w base) (fit : dict.Fits w base) (width : dict.bits=(a*K)*M)
    (static_ : ∀x : Cell ((a*K)*M),m (dict.base+x.val)=((DescentSIMDLookup.table (M:=M) (count (a:=a) (K:=K) b) x).val:Word w)) (j:Fin (D*r)) :
    Source (expr P old dict H j) (fun h g=>value walks prev b h g j) M m :=by
  let z:=finProdFinEquiv.symm j
  let x:=fun h g=>(DescentSortedRoster.indexed walks h z.1).elim 0 (fun v=>prev z.2 v g)
  have issued:=peerSource P (old z.2) base (access _) _ m mounted (prev z.2) (stored _) z.1
  intro p
  have small:(data x p).val<dict.size:=by simpa only [Bank.size,width] using (data x p).isLt
  change dict.read m ((peerExpr P (old z.2) H z.1).eval m _)=_
  rw [issued,bank_read _ _ small fit,static_]
  apply congrArg (fun z : Cell (b*M)=>(z.val:Word w))
  simp only [DescentSIMDLookup.table,data,Equiv.symm_apply_apply];apply congrArg (encode b M);funext i
  change count (a:=a) (K:=K) b
      (if hg : p.2.val*M+i.val<G then x p.1 ⟨p.2.val*M+i.val,hg⟩ else 0) =
    (if hg : p.2.val*M+i.val<G then value walks prev b p.1 ⟨p.2.val*M+i.val,hg⟩ j else 0)
  by_cases live : p.2.val*M+i.val<G
  · simp only [dite_eq_left live]
    exact count_peer (b:=b) (a:=a) (K:=K) (DescentSortedRoster.indexed walks p.1 z.1)
      (fun v=>prev z.2 v ⟨p.2.val*M+i.val,live⟩)
  · simp only [dite_eq_right live]
    exact empty

theorem counts (P : Ports D) (old : Fin r→Bank) (dict : Bank) (fields : Fin (D*r)→Tables) (base : ℕ) (m : Memory w)
    (walks : Fin H→Fin D→Option (Fin H)) (prev : Fin r→Fin H→Fin G→Cell (a*K))
    (mounted : Mounted P (DescentSortedRoster.indexed walks) m G M) (stored : ∀x,Reads (old x) (prev x) M m)
    (access : ∀x,Accessible P (old x) H G M w base) (fit : dict.Fits w base) (width : dict.bits=(a*K)*M)
    (static_ : ∀x : Cell ((a*K)*M),m (dict.base+x.val)=((DescentSIMDLookup.table (M:=M) (count (a:=a) (K:=K) b) x).val:Word w))
    (fitted : Gather.Bounds (w:=w) (d:=b) (M:=M) fields (expr P old dict H) base)
    (tables : ∀j,Static (fields j) (Gather.setField (d:=b) j) M m) :
    Source (Gather.assembly fields (expr P old dict H)) (fun h g=>encode b (D*r) (value walks prev b h g)) M m :=by
  simpa only [Gather.assembly,List.mem_finRange,ite_true] using Gather.collected fields (expr P old dict H) base fitted m tables (value walks prev b)
    (source P old dict base m walks prev mounted stored access fit width static_) (List.finRange (D*r))

def direct (P : Ports D) (old : Fin r→Bank) (H : ℕ) (j : Fin (D*r)) :=
  let z:=finProdFinEquiv.symm j;peerExpr P (old z.2) H z.1

def priorValue (walks : Fin H→Fin D→Option (Fin H)) (prior : Fin r→Fin H→Fin G→Cell b)
    (h : Fin H) (g : Fin G) (j : Fin (D*r)) :=
  let z:=finProdFinEquiv.symm j;(DescentSortedRoster.indexed walks h z.1).elim 0 (fun v=>prior z.2 v g)

/-- The same physical donor geometry carries charged population if that
column was already supplied by the preceding ordinary or reset stage. -/
theorem fromCounts (P : Ports D) (old : Fin r→Bank) (fields : Fin (D*r)→Tables) (base : ℕ) (m : Memory w)
    (walks : Fin H→Fin D→Option (Fin H)) (prior : Fin r→Fin H→Fin G→Cell b)
    (mounted : Mounted P (DescentSortedRoster.indexed walks) m G M) (stored : ∀x,Reads (old x) (prior x) M m)
    (access : ∀x,Accessible P (old x) H G M w base)
    (fits : Gather.Bounds (w:=w) (d:=b) (M:=M) fields (direct P old H) base) (statics : ∀j,Static (fields j) (Gather.setField (d:=b) j) M m) :
    Source (Gather.assembly fields (direct P old H)) (fun h g=>encode b (D*r) (priorValue walks prior h g)) M m :=by
  have fetch (j : Fin (D*r)) : Source (direct P old H j) (fun h g=>priorValue walks prior h g j) M m :=
    peerSource P _ base (access _) _ m mounted _ (stored _) _
  simpa only [Gather.assembly,List.mem_finRange,ite_true] using Gather.collected fields (direct P old H) base fits m statics (priorValue walks prior) fetch (List.finRange (D*r))

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts

end OAI
