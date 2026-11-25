import OAI.Hierarchy.DescentDenseHostOrder
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Raw trunk endpoints in the rectangular installed host directory -/
namespace Hierarchy.DescentResetTrunkPalette
open DescentDenseHostOrder DescentCommonHost ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (r dep : ℕ)
local notation "palette" => roster G r dep
local notation "shape_" => Node Unit (Unit×DescentContacts.Endpoint (2^n)) (DescentCommonPalette.rotor G).Site

def order : ↥palette≃Fin (palette).card :=Equiv.ofBijective (localRank G r dep)
  ((Fintype.bijective_iff_injective_and_card _).2 ⟨(localRank G r dep).injective,by simp⟩)

def flip (s : Bool) : shape_→Option shape_
  | .trunk _ z=>some (.trunk s z)
  | _=>none

/-- Per rectangular host these are the actual two raw host IDs for its trunk
shape. All decisions use only the common finite shape alphabet and a fixed
mixed-radix address. The graph of a particular permutation is never read. -/
def pointer {H : ℕ} (side : Bool) (idx : Fin (H*(palette).card)) : Option (Fin (H*(palette).card)) := do
  let (root,tag):=finProdFinEquiv.symm idx
  let key←flip G side ((order G r dep).symm tag).val
  if yes : key∈palette then
    return finProdFinEquiv (root,(order G r dep) ⟨key,yes⟩)
  else none

def badge {H : ℕ} (idx : Fin (H*(palette).card)) : Bool:=
  let info : Fin H×Fin (palette).card:=finProdFinEquiv.symm idx
  match ((order G r dep).symm info.2).val with
  | .trunk _ z=>z.2.2.isSome
  | _=>false

theorem at_label {H : ℕ} (root : Fin H) (a v : ↥palette) (s : Bool)
    (good : flip G s a.val=some v.val) :
    pointer G r dep s (finProdFinEquiv (root,localRank G r dep a))=
      some (finProdFinEquiv (root,localRank G r dep v)) := by
  change pointer G r dep s (finProdFinEquiv (root,(order G r dep) a))=
    some (finProdFinEquiv (root,(order G r dep) v))
  simp [pointer,good,v.property]

theorem off_label {H : ℕ} (root : Fin H) (a : ↥palette) (s : Bool) (good : flip G s a.val=none) :
    pointer G r dep s (finProdFinEquiv (root,localRank G r dep a))=none :=by
  change pointer G r dep s (finProdFinEquiv (root,(order G r dep) a))=_
  simp [pointer,good]

theorem at_badge {H : ℕ} (root : Fin H) (a : ↥palette) (s : Bool) (key)
    (good : a.val=.trunk s key) : badge G r dep (finProdFinEquiv (root,localRank G r dep a))=key.2.2.isSome := by
  change badge G r dep (finProdFinEquiv (root,(order G r dep) a))=_
  simp [badge,good]

/-- Both trunk sides belong to the shape alphabet, including the unoccupied
rectangular rows. No test of the current stage's concrete genealogy is needed. -/
theorem flip_live (a : ↥palette) (s j : Bool) (key)
    (shapeAt : a.val=.trunk s key) : .trunk j key∈palette:=by
  obtain ⟨⟨old,v,code,body⟩,_,seen⟩:=Finset.mem_image.mp a.property
  have eqn:=seen.trans shapeAt
  rcases body with tag | cell | ⟨tag,loc⟩
  · have keys:=(Node.trunk.inj eqn).2
    refine Finset.mem_image.mpr ⟨(j,v,code,.inl tag),Finset.mem_univ _,?_⟩
    exact congrArg (Node.trunk j) keys
  · simp [render] at eqn
  · simp [render] at eqn

def description {H : ℕ} (i : Fin (H*(palette).card)) : Option (Fin (H*(palette).card)×Fin (H*(palette).card)×Bool):=do
  let left←pointer G r dep false i
  let right←pointer G r dep true i
  return (left,right,badge G r dep i)

theorem description_at {H : ℕ} (i : Fin (H*(palette).card)) :
    (description G r dep i).map Prod.fst=pointer G r dep false i ∧
    (description G r dep i).map (fun a=>a.2.1)=pointer G r dep true i ∧
    (description G r dep i).elim 0 (fun a=>a.2.2.toNat)=(badge G r dep i).toNat:=by
  obtain ⟨⟨v,tag⟩,rfl⟩:=finProdFinEquiv.surjective i
  obtain ⟨q,rfl⟩:=(order G r dep).surjective tag
  cases found : q.val with
  | good=>
    simp [description,pointer,flip,badge,found]
  | fall=>
    simp [description,pointer,flip,badge,found]
  | trunk s key=>
    have l:=flip_live G r dep q s false key found
    have r:=flip_live G r dep q s true key found
    simp [description,pointer,flip,badge,found,l,r]

def value {H : ℕ} (col : Fin 3) (i : Fin (H*(palette).card)) : ℕ:=
  if col=2 then (badge G r dep i).toNat else
    (pointer G r dep (decide (col=1)) i).elim (H*(palette).card) Fin.val

def literals (H : ℕ) (j : ℕ) : ℕ:=
  if hit : j<3*(H*(palette).card) then
    let p : Fin 3×Fin (H*(palette).card):=finProdFinEquiv.symm ⟨j,hit⟩
    value G r dep p.1 p.2
  else 0

def program (w base H : ℕ):=DescentStaticWordColumn.program w base (literals G r dep H) (3*(H*(palette).card))
def memory {w : ℕ} (base H : ℕ) (m : Memory w):=
  DescentStaticWordColumn.image base (literals G r dep H) m (3*(H*(palette).card))

theorem run {w : ℕ} (base H : ℕ) (m : Memory w) (room : base+3*(H*(palette).card)<2^w) :
    let p:=program G r dep w base H
    let done:=memory G r dep base H m
    p.Exec m done (4+10*(3*(H*(palette).card))) ∧
      (∀(col : Fin 3) (i : Fin (H*(palette).card)),done (base+col.val*(H*(palette).card)+i.val)=(value G r dep col i:Word w)) ∧
      (∀a,a<base ∨ base+3*(H*(palette).card)≤a→done a=m a) ∧
      DescentStaticWordColumn.names p=15*(3*(H*(palette).card)+1) ∧ CheapCode p:=by
  intro p done
  let count := 3 * (H * (palette).card)
  let data := literals G r dep H
  refine ⟨DescentStaticWordColumn.mount base count data m room, ?_,
    DescentStaticWordColumn.frame base count data m,
    DescentStaticWordColumn.names_mount w base data count,
    DescentStaticWordColumn.cheap w base data count⟩
  · intro col i
    let pos:=finProdFinEquiv (col,i)
    have off : pos.val=col.val*(H*(palette).card)+i.val:=by simp [pos,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
    rw [Nat.add_assoc, ← off]
    exact (DescentStaticWordColumn.read base count data m pos.isLt).trans (by
      simp only [data, literals, dite_eq_left pos.isLt]
      change (value G r dep (finProdFinEquiv.symm pos).1
        (finProdFinEquiv.symm pos).2 : Word w) = _
      have decode : finProdFinEquiv.symm pos = (col,i) := finProdFinEquiv.symm_apply_apply _
      rw [decode])

end
end Hierarchy.DescentResetTrunkPalette

end OAI
