import OAI.Hierarchy.DescentContactTree
import OAI.Hierarchy.DescentLocalTables
import OAI.Computability.BorderVNP.BitVolume
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Literal binary fallback contact trees for arbitrarily indexed original bundles -/

namespace Hierarchy.DescentContactTree.Physical
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {I : Type} [Fintype I] (dest : I→ℕ→Bool) (wt : I→ℕ)
variable {D h : ℕ}

abbrev Site (h : ℕ) := Σ k : Fin (h+1),Node k.val
abbrev Edge (h : ℕ) := Σ k : Fin h,Node (k.val+1)
abbrev Terminal (h : ℕ) := Unit ⊕ Node h
abbrev Row := (i : I) → Fin (wt i) → Bool

def nodeWidth (k : ℕ) (v : Node k) := ∑ i : Cell dest k v,wt i.val

def terminalWidth (h : ℕ) : Terminal h → ℕ
  | .inl _ => ∑ i,wt i
  | .inr v => nodeWidth dest wt h v

def graph (D h : ℕ) : Network D (Terminal h) (terminalWidth dest wt h) where
  Site := Site h
  Edge := Edge h
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := ⟨e.1.castSucc,fun i=>e.2 i.castSucc⟩
  dst e := ⟨e.1.succ,e.2⟩
  width e := nodeWidth dest wt (e.1.val+1) e.2
  attach
    | .inl _ => ⟨0,finZeroElim⟩
    | .inr v => ⟨Fin.last _,v⟩
  position _ := 0
  in_ball _ := by simp

/-- A named sublist contains one coordinate for each bit of every bundle in
the cell. The encoding is fixed before either boundary word is supplied. -/
def concat {A : Type*} [Fintype A] (lens : A→ℕ) : (Fin (∑i,lens i)→Bool) ≃ ((i:A)→Fin (lens i)→Bool) :=
  let addr : (Σi,Fin (lens i)) ≃ Fin (∑i,lens i) :=
    (Fintype.equivFin _).trans (finCongr (by simp))
  (Equiv.arrowCongr addr.symm (Equiv.refl _)).trans (Equiv.piCurry (fun _ _=>Bool))

def childCode (k : ℕ) (v : Node k) := concat (fun i : Cell dest k v=>wt i.val)

/-- Each of the h internal wire levels contains a partition of the actual
identity set I. A whole-network assignment gives precisely h full rows. -/
def hidden : (graph dest wt D h).Assignment ≃ (Fin h → Row wt) :=
  (Equiv.piCurry (fun k : Fin h=>fun v : Node (k.val+1)=>Fin (nodeWidth dest wt _ v)→Bool)).trans
    (Equiv.piCongrRight fun k=>
      (Equiv.piCongrRight fun v=>childCode dest wt (k.val+1) v).trans
        (packed (fun i=>Fin (wt i)→Bool) dest (k.val+1)).symm)

def exposed (x y : Row wt) : Ports (terminalWidth dest wt h)
  | .inl _ => (concat wt).symm x
  | .inr v => (childCode dest wt h v).symm (fun i=>y i.val)

def top (p : Ports (terminalWidth dest wt h)) : Row wt := concat wt (p (.inl ()))
def ground (p : Ports (terminalWidth dest wt h)) : Row wt :=
  fun i=> childCode dest wt h (prefixAt dest h i) (p (.inr (prefixAt dest h i))) ⟨i,rfl⟩

@[simp] theorem top_exposed (x y : Row wt) : top dest wt (h:=h) (exposed dest wt x y)=x := by simp [top,exposed]
@[simp] theorem ground_exposed (x y : Row wt) : ground dest wt (h:=h) (exposed dest wt x y)=y := by
  funext i
  simp [ground,exposed]

def incoming (x : Row wt) (z : Fin h→Row wt) : Fin (h+1) → Row wt := Fin.cases x z
def outgoing (y : Row wt) (z : Fin h→Row wt) : Fin (h+1) → Row wt := Fin.lastCases y z

variable {K : Type*} [CommSemiring K]

def relayFactor (a : (graph dest wt D h).Assignment) (pins : Ports (terminalWidth dest wt h)) (q : Site h) : K :=
  let z := hidden dest wt a
  if ∀ i : Cell dest q.1.val q.2,incoming wt (top dest wt pins) z q.1 i.val=
    outgoing wt (ground dest wt pins) z q.1 i.val then 1 else 0

private theorem incoming_local (a b : (graph dest wt D h).Assignment) (x y : Ports (terminalWidth dest wt h))
    (k : Fin (h+1)) (i : I)
    (cables : ∀e,(graph dest wt D h).src e=⟨k,prefixAt dest k.val i⟩ ∨
      (graph dest wt D h).dst e=⟨k,prefixAt dest k.val i⟩ → a e=b e)
    (pins : ∀p,(graph dest wt D h).attach p=⟨k,prefixAt dest k.val i⟩ → x p=y p) :
    incoming wt (top dest wt x) (hidden dest wt a) k i=incoming wt (top dest wt y) (hidden dest wt b) k i := by
  revert cables pins
  refine Fin.cases ?_ (fun t=>?_) k
  · intro _ p
    have kept := p (.inl ()) (congrArg (fun v : Node 0 => (⟨0,v⟩ : Site h))
      (Subsingleton.elim finZeroElim (prefixAt dest 0 i)))
    simp [incoming,top,kept]
  · intro c _
    have kept := c ⟨t,prefixAt dest (t.val+1) i⟩ (Or.inr rfl)
    change childCode dest wt _ _ (a _) ⟨i,rfl⟩=childCode dest wt _ _ (b _) ⟨i,rfl⟩
    rw [kept]

private theorem outgoing_local (a b : (graph dest wt D h).Assignment) (x y : Ports (terminalWidth dest wt h))
    (k : Fin (h+1)) (i : I)
    (cables : ∀e,(graph dest wt D h).src e=⟨k,prefixAt dest k.val i⟩ ∨
      (graph dest wt D h).dst e=⟨k,prefixAt dest k.val i⟩ → a e=b e)
    (pins : ∀p,(graph dest wt D h).attach p=⟨k,prefixAt dest k.val i⟩ → x p=y p) :
    outgoing wt (ground dest wt x) (hidden dest wt a) k i=outgoing wt (ground dest wt y) (hidden dest wt b) k i := by
  revert cables pins
  refine Fin.lastCases ?_ (fun t=>?_) k
  · intro _ p
    have kept := p (.inr (prefixAt dest h i)) rfl
    simp [outgoing,ground,kept]
  · intro c _
    let e : Edge h := ⟨t,prefixAt dest (t.val+1) i⟩
    have kept := c e (Or.inl rfl)
    simp only [outgoing,Fin.lastCases_castSucc]
    exact congrArg (fun word => childCode dest wt (t.val+1) e.2 word ⟨i,rfl⟩) kept

theorem supported : DescentLocalTables.Supported (graph dest wt D h) (relayFactor (K:=K) dest wt) := by
  rintro ⟨k,v⟩ a b x y cables pins
  have both (i : Cell dest k.val v) :
      (incoming wt (top dest wt x) (hidden dest wt a) k i.val=outgoing wt (ground dest wt x) (hidden dest wt a) k i.val) ↔
      (incoming wt (top dest wt y) (hidden dest wt b) k i.val=outgoing wt (ground dest wt y) (hidden dest wt b) k i.val) := by
    rcases i with ⟨i,rfl⟩
    rw [incoming_local dest wt a b x y k i cables pins,outgoing_local dest wt a b x y k i cables pins]
  unfold relayFactor
  simp only
  exact if_congr (forall_congr' both) rfl rfl

def tables := DescentLocalTables.tables (graph dest wt D h) (relayFactor (K:=K) dest wt)

private theorem one_level (k : Fin (h+1)) (x y : Row wt) (z : Fin h→Row wt) :
    (∏ v : Node k.val,if ∀i : Cell dest k.val v,incoming wt x z k i.val=outgoing wt y z k i.val then (1:K) else 0) =
      if incoming wt x z k=outgoing wt y z k then 1 else 0 := by
  by_cases eq : incoming wt x z k=outgoing wt y z k
  · simp [eq]
  · obtain ⟨i,ne⟩ := Function.ne_iff.mp eq
    rw [ite_eq_right eq]
    exact Finset.prod_eq_zero (Finset.mem_univ (prefixAt dest k.val i))
      (ite_eq_right (fun all=>ne (all ⟨i,rfl⟩)))

omit [Fintype I] in
private theorem chain (x y : Row wt) (z : Fin h → Row wt) :
    (∀k,incoming wt x z k=outgoing wt y z k) ↔ z=(fun _=>x) ∧ x=y := by
  constructor
  · intro equal
    have first (k : Fin (h+1)) : incoming wt x z k=x := by
      refine Fin.induction rfl (fun t ih=>?_) k
      simpa [incoming,outgoing] using (equal t.castSucc).symm.trans ih
    refine ⟨funext fun k=>first k.succ,?_⟩
    simpa [outgoing] using (first (Fin.last h)).symm.trans (equal (Fin.last h))
  · rintro ⟨rfl,rfl⟩ k
    have a : ∀k : Fin (h+1),incoming wt x (fun _=>x) k=x := Fin.cases rfl (fun _=>rfl)
    have b : ∀k : Fin (h+1),outgoing wt x (fun _=>x) k=x := Fin.lastCases (by simp [outgoing]) (fun _=>by simp [outgoing])
    rw [a,b]

/-- The internal tensor sum is an equality router for the original named
bundles. Each leaf carries the sublist belonging to its actual destination. -/
theorem value (x y : Row wt) : (graph dest wt D h).value (tables (K:=K) dest wt) (exposed dest wt x y) =
    if x=y then 1 else 0 := by
  have point (a : (graph dest wt D h).Assignment) :
      (∏v,(graph dest wt D h).read (tables (K:=K) dest wt) a (exposed dest wt x y) v) =
      if hidden dest wt a=(fun _=>x) ∧ x=y then 1 else 0 := by
    simp_rw [tables,DescentLocalTables.read _ _ (supported dest wt)]
    change (∏ v : Site h, relayFactor dest wt a (exposed dest wt x y) v) = _
    rw [Fintype.prod_sigma (fun v : Site h => relayFactor dest wt a (exposed dest wt x y) v)]
    simp only [relayFactor,top_exposed,ground_exposed]
    simp_rw [one_level]
    have route := chain wt x y (hidden dest wt a)
    by_cases eq : ∀k,incoming wt x (hidden dest wt a) k=outgoing wt y (hidden dest wt a) k
    · rw [ite_eq_left (route.mp eq)]
      exact Finset.prod_eq_one (fun k _ => ite_eq_left (eq k))
    · rw [ite_eq_right (fun agree => eq (route.mpr agree))]
      obtain ⟨k,ne⟩ := not_forall.mp eq
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right ne)
  unfold Network.value
  simp_rw [point]
  rw [←(hidden (D:=D) (h:=h) dest wt).symm.sum_comp (fun a=>
    if hidden dest wt a=(fun _=>x) ∧ x=y then (1:K) else 0)]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single (fun _ : Fin h=>x)]
  · simp
  · intro a _ ne
    simp [ne]
  · simp

/-- Every bundle traverses precisely one wire at each of the h levels. -/
theorem wire_cost : (∑e,(graph dest wt D h).width e)=h*∑i,wt i := by
  change (∑e : Edge h,nodeWidth dest wt (e.1.val+1) e.2)=_
  rw [Fintype.sum_sigma]
  simp [nodeWidth,level_width,smul_eq_mul]

theorem port_cost : (∑p : Terminal h,terminalWidth dest wt h p)=2*∑i,wt i := by
  rw [Fintype.sum_sum_type]
  simp [terminalWidth,nodeWidth,level_width,two_mul]

end
end Hierarchy.DescentContactTree.Physical

end OAI
