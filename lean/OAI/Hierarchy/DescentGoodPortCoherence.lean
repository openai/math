import OAI.Hierarchy.DescentCanonicalObserved
import OAI.Hierarchy.DescentChosenContactBudget
import OAI.Hierarchy.DescentRelabeledRotor

namespace OAI
/-! # Installed rotor peers in the common host of every surviving block -/

namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentRotor DescentCanonicalPorts
open scoped Classical BigOperators
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k m n : ℕ}
local notation "Y" => (2^n:ℕ)
variable (P : Placement V I H A k (2^n))

def Placement.outputName (m : ℕ) (s : Bool) (c : Reserve P.span) : (V×ℕ)×Fin Y :=
  let z := slot P.b P.keys P.hub P.ends P.span P.room s c
  (short (m:=m) P.b z.1.val,P.columns s z.1 z.2)

def Placement.CommonOutputs (m : ℕ) : Prop :=
  ∀s c d,P.outputName m s c=P.outputName m s d→P.outputName m (!s) c=P.outputName m (!s) d

/-- Publicly readable prefix of the potential incoming contacts at this row.
The full candidate list is determined by the two old host rows and their
relative dyadic intervals. -/
def Placement.reservedColumn (m : ℕ) (host : V↪ℕ) (near : V→Finset V)
    (size : V→V→ℕ) (s : Bool) (c : Reserve P.span) : ℕ :=
  let x:=short (m:=m) P.b (P.ends s c.1).val
  let y:=short (m:=m) P.b (P.ends (!s) c.1).val
  (∑a ∈ Finset.univ.filter (fun a : Potential (m:=m) near P.b x.1 x.2=>
      potentialNumber near P.b host x.1 x.2 a<Nat.pair (host y.1) y.2),size x.1 a.1.val)+c.2.val

structure Placement.ColumnRoster (m : ℕ) where
  host : V↪ℕ
  near : V→Finset V
  size : V→V→ℕ
  read : ∀s (c : Reserve P.span),(P.outputName m s c).2.val=P.reservedColumn m host near size s c
  span : ∀s a,P.span a=size (P.ends s a).val.1 (P.ends (!s) a).val.1

namespace Dyadic
variable {B S unit : ℝ} {g Δ K : ℕ} (D : Dyadic V I k) (L : D.Loads (2^n) B S unit)
variable (pos : 0<S) (pu : 0<unit) (ub : unit≤B) (ys : ((2^n : ℕ):ℝ)*B≤S)
variable (fall : Bool→V×Block k→H)
variable (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
variable (adj : ∀i : D.Paid,(D.old true i.val).1∈near (D.old false i.val).1)
variable (same : ∀i : D.Paid,(D.old true i.val).2=(D.old false i.val).2)
variable (low : ∀v,m≤D.b v) (cap : V→V→ℝ)
variable (amount : ∀a s,L.cap a=cap (D.endAt s a).val.1 (D.endAt (!s) a).val.1)
variable (nonneg : ∀v w,0≤cap v w)
variable (paid : ∀v id,(∑w∈near v,∑_j∈DescentBaseProfile.touching (D.b v) (D.b w) id,cap v w)≤2*S)
variable (smooth : ∀v w,w∈near v→D.b w≤D.b v+g) (degree : ∀v,(near v).card≤Δ)
variable (budget : Δ*2^g≤K) (space : 4*K≤2^n)
local notation "P₀" => D.install L pos pu ub ys fall

include sym adj same low amount nonneg paid smooth degree budget space in
theorem install_columns : ∃σ : Bool→D.G→Equiv.Perm (Fin Y),(relabel P₀ σ).CommonOutputs m ∧
    ∀s (c : Reserve (D.span L)),((relabel P₀ σ).outputName m s c).2.val=
      (relabel P₀ σ).reservedColumn m D.hostNumber near (fun v w=>DescentBaseProfile.rowCount Y S (cap v w)) s c := by
  classical
  choose σ agree using extend_output D near sym adj same low L pos pu cap amount nonneg paid smooth degree budget space
  refine ⟨σ,?_⟩
  let sock := socketName D near sym adj same low L cap amount
  let rows := rowName near D.b low cap S pos nonneg paid smooth degree budget space D.hostNumber
  have get (s : Bool) (c : Reserve (D.span L)) :
      (relabel P₀ σ).outputName m s c=rows (sock s c) := by
    refine Prod.ext ?_ ?_
    · rfl
    · exact agree s (D.endAt s c.1) ⟨⟨c.1,rfl⟩,c.2⟩
  constructor
  · intro s c d eq
    have key : rows (sock s c) = rows (sock s d) :=
      (get s c).symm.trans (eq.trans (get s d))
    have opposite := same_peer D near sym adj same low L pos cap amount nonneg paid smooth degree budget space s c d key
    exact (get (!s) c).trans (opposite.trans (get (!s) d).symm)

  · intro s c
    rw [get]
    rfl

include sym adj same low amount nonneg paid smooth degree budget space in
theorem install_common : ∃σ : Bool→D.G→Equiv.Perm (Fin Y),(relabel P₀ σ).CommonOutputs m := by
  obtain ⟨σ,ok,_⟩:=D.install_columns L pos pu ub ys fall near sym adj same low cap amount nonneg paid smooth degree budget space
  exact ⟨σ,ok⟩

end Dyadic
end
end Hierarchy.DescentChosenRouter

end OAI
