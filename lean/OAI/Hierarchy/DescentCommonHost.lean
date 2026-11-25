import OAI.Hierarchy.DescentCommonPalette
import OAI.Hierarchy.DescentCommonResetLinks

namespace OAI
/-! # Common trivalent reset adjacency after dropping the coarse block -/

namespace Hierarchy.DescentCommonHost
open DescentChosenRouter DescentContacts DescentCanonicalPorts DescentRelativeContacts
open scoped Classical
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
    {k n h : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)

/-- Hardware positions explicitly retain the shape of the configured gadget.
The course block is erased from the base and terminal labels. -/
inductive Node (V Z J : Type) where
  | trunk (s : Bool) (z : Z)
  | good (s : Bool) (base : V×ℕ) (cell : J)
  | fall (s : Bool) (z : Z) (digits : List Bool)
  deriving DecidableEq

local notation "Z" => V×Endpoint (2^n)
local notation "R" => DescentCommonPalette.rotor G
local notation "X" => Node V Z (Computability.BorderVNP.Crossing.Network.Site R)
variable (m : ℕ) (code : H ↪ V × Endpoint (2 ^ n))
local notation "lab" => fun t=>shortName m (code t)

def goodName (q : (V×ℕ)×Fin (2^n)) : Z := (q.1.1,((P.b q.1.1-m,q.1.2),some q.2))
def readGood (z : Z) : Option ((V×ℕ)×Fin (2^n)) :=
  z.2.2.map (fun j=>((z.1,z.2.1.2),j))

theorem read_good (q : (V×ℕ)×Fin (2^n)) : readGood (goodName P m q)=some q := rfl

def direct (s : Bool) : (((V×ℕ)×Fin (2^n)) ⊕ (Z×List Bool)) → X
  | .inl (base,row) => .good s base ((R).attach (row,true))
  | .inr (z,digits) => .fall s z digits

def fallHeight (s : Bool) (z : Z) :=
  if live : ∃t,lab t=z then (P.fallbackBook s live.choose).height else 0

theorem height_at (proof : P.CommonFallback lab) (s : Bool) (t : H) :
    fallHeight P m code s (lab t)=(P.fallbackBook s t).height := by
  have live : ∃q,lab q=lab t := ⟨t,rfl⟩
  rw [fallHeight,dite_eq_left live]
  exact proof.1 s _ _ live.choose_spec

def goodExt (s : Bool) (b : V×ℕ) : DescentRotor.Physical.Pin (2^n)→Option X
  | (j,false) => some (.trunk s (goodName P m (b,j)))
  | (j,true) => (linkPeer P lab m s (.inl (b,j))).map (direct G (!s))

def fallExt (s : Bool) (z : Z) {t : ℕ} : DescentContactTree.Physical.Terminal t→Option X
  | .inl _ => some (.trunk s z)
  | .inr y => (linkPeer P lab m s (.inr (z,List.ofFn y))).map (direct G (!s))

def goodNear (s : Bool) (b : V×ℕ) (x : (R).Site) : Finset X :=
  DescentCommonPalette.near R (.good s b) (goodExt P G m code s b) x

def treeNear (s : Bool) (z : Z) {t : ℕ} (x : (DescentCommonPalette.tree t).Site) : Finset X :=
  DescentCommonPalette.near (DescentCommonPalette.tree t) (fun v=>.fall s z (DescentCommonPalette.path v))
    (fallExt P G m code s z) x

def fallNear (s : Bool) (z : Z) (ds : List Bool) : Finset X :=
  if found : ∃x : (DescentCommonPalette.tree (fallHeight P m code s z)).Site,DescentCommonPalette.path x=ds
    then treeNear P G m code s z found.choose else ∅

theorem fallNear_at (s : Bool) (z : Z) {t : ℕ} (eqn : fallHeight P m code s z=t)
    (x : (DescentCommonPalette.tree t).Site) :
    fallNear P G m code s z (DescentCommonPalette.path x)=treeNear P G m code s z x := by
  subst t
  have found : ∃v : (DescentCommonPalette.tree (fallHeight P m code s z)).Site,
    DescentCommonPalette.path v=DescentCommonPalette.path x := ⟨x,rfl⟩
  rw [fallNear,dite_eq_left found,DescentCommonPalette.path_injective found.choose_spec]

/-- Three candidates at an old stand, including its opposite trunk stand.
Unoccupied paid or exceptional sockets only enlarge the possible neighborhood. -/
def trunkNear (s : Bool) (z : Z) : Finset X :=
  insert (.trunk (!s) z) (insert (.fall s z []) ((readGood z).map
    (fun q=>(Node.good s q.1 ((R).attach (q.2,false)) : X))).toFinset)

def near : X→Finset X
  | .trunk s z => trunkNear G s z
  | .good s b x => goodNear P G m code s b x
  | .fall s z ds => fallNear P G m code s z ds

theorem degree (x : X) : (near P G m code x).card≤3 := by
  cases x with
  | trunk s z =>
    unfold near trunkNear
    apply (Finset.card_insert_le _ _).trans
    apply Nat.succ_le_succ
    apply (Finset.card_insert_le _ _).trans
    apply Nat.succ_le_succ
    cases readGood z <;> simp
  | good s b x =>
    exact (DescentCommonPalette.near_size (DescentCommonPalette.rotor G)
      (fun v => (Node.good s b v : X)) (goodExt P G m code s b) x).trans
      (DescentCommonPalette.rotor_degree G x)
  | fall s z ds =>
    change (fallNear P G m code s z ds).card≤3
    unfold fallNear
    split
    · rename_i found
      exact (DescentCommonPalette.near_size (DescentCommonPalette.tree (fallHeight P m code s z))
        (fun v => (Node.fall s z (DescentCommonPalette.path v) : X))
        (fallExt P G m code s z) found.choose).trans
        (DescentCommonPalette.tree_degree _ found.choose)
    · simp

end
end Hierarchy.DescentCommonHost

end OAI
