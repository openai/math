import OAI.Hierarchy.DescentTerminalOriginalExterior
import OAI.Hierarchy.DescentExteriorSpine

namespace OAI
/-! # A remixed terminal row has one actual graph position -/

namespace Hierarchy.DescentTerminalExteriorPackets
open DescentGL DescentColonies DescentExterior
open scoped Classical
noncomputable section
variable {j r E b f : ℕ} {A V : Type}
local notation "k" => j+(j+r)
local notation "P" => Σ _:Fin (2^k),Fin E
variable {start : (Σ _ : Fin (2 ^ (j + (j + r))), Fin E) → Bits (j + (j + r))}
    {live : (Σ _ : Fin (2 ^ (j + (j + r))), Fin E) → Bits b}
    {before : (Σ _ : Fin (2 ^ (j + (j + r))), Fin E) → A}
    {after : (Σ _ : Fin (2 ^ (j + (j + r))), Fin E) → V}
    (s : Spine start live before after f)

/-- Place the active coordinates last. Thus changing any of the low stack
digits never changes the frozen ancestry of the current physical position. -/
def frozenFirst (sp : Spine start live before after f) : Layout k :=
  ((sp.cut.trans (LinearEquiv.prodComm (ZMod 2) (Bits b) (Bits f))).trans (splitRows f b).symm).trans
    (castBits ((Nat.add_comm f b).trans sp.width))

theorem frozen_digit (x : Bits k) :
    (address k (frozenFirst s x)).val/2^b=(address f (s.cut x).2).val := by
  let y:=(splitRows f b).symm ((s.cut x).2,(s.cut x).1)
  change (address _ (castBits _ y)).val/2^b=_
  rw [address_cast]
  have h : (address (f+b) y).val=(address f (s.cut x).2).val*2^b+(address b (s.cut x).1).val := by
    simpa only [y,LinearEquiv.apply_symm_apply] using split_value f b y
  rw [h,Nat.mul_comm (address f (s.cut x).2).val (2^b),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt (address b (s.cut x).1).isLt,Nat.add_zero]

theorem row_high (v : Bits k) :
    (address k v).val/2^j=(rowOrd j r (coords j r v).2).val := by
  rw [coordinate_row,Nat.mul_comm (rowOrd j r (coords j r v).2).val (2^j),Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (chunkOrd j (coords j r v).1).isLt,Nat.add_zero]

def rotor (sp : Spine start live before after f) (seed : Fin E→Layout k) (e : Fin E) : Layout k :=
  (seed e).trans (frozenFirst sp)

theorem row_frozen (seed : Fin E→Layout k) (room : j≤b)
    (opened : ∀u:P,start u=seed u.2 ((address k).symm u.1))
    (u v : P)
    (same : (chart (j:=j) (r:=r) (rotor s seed) u).1=(chart (rotor s seed) v).1) : (s.cut (start u)).2=(s.cut (start v)).2 := by
  have both:=finProdFinEquiv.injective same
  have slabEq : u.2=v.2:=congrArg Prod.fst both
  have high : (rowOrd j r (coords j r (frozenFirst s (start u))).2).val=
      (rowOrd j r (coords j r (frozenFirst s (start v))).2).val := by
    rw [opened u,opened v]
    exact congrArg (fun a=>a.2.val) both
  have divj:=((row_high (frozenFirst s (start u))).trans high).trans
    (row_high (frozenFirst s (start v))).symm
  have full:=congrArg (fun n:ℕ=>n/2^(b-j)) divj
  simp only [Nat.div_div_eq_div_mul,←pow_add,Nat.add_sub_of_le room,
    frozen_digit] at full
  exact (address f).injective (Fin.ext full)

theorem one_home (seed : Fin E→Layout k) (room : j≤b)
    (opened : ∀u:P,start u=seed u.2 ((address k).symm u.1))
    (sameSlab : ∀u v:P,u.2=v.2→before u=before v) (u v : P)
    (same : (chart (j:=j) (r:=r) (rotor s seed) u).1=(chart (rotor s seed) v).1) : after u=after v := by
  have both:=finProdFinEquiv.injective same
  exact s.host_eq u v (sameSlab u v (congrArg Prod.fst both)) (row_frozen s seed room opened u v same)

theorem separate (seed : Fin E→Layout k) (room : j≤b)
    (opened : ∀u:P,start u=seed u.2 ((address k).symm u.1)) (u v:P)
    (same : (chart (j:=j) (r:=r) (rotor s seed) u).1=(chart (rotor s seed) v).1)
    (active : live u=live v) : u=v := by
  have slabEq := congrArg Prod.fst (finProdFinEquiv.injective same)
  have eqn : start u=start v := by
    apply s.cut.injective;apply Prod.ext
    · simpa only [s.active_eq] using active
    · exact row_frozen s seed room opened u v same
  rw [opened u,opened v] at eqn
  rcases u with ⟨u,a⟩;rcases v with ⟨v,b⟩
  change a=b at slabEq;subst b
  exact congrArg (fun i:Fin (2^k)=> (⟨i,a⟩:P)) ((address k).symm.injective ((seed a).injective eqn))

/-- The single directory read for this whole row is the genuine common
position at its zero lane. The other lanes use the same read by the preceding
coordinate theorem, including different original copies on one slab. -/
def owner (sp : Spine start live before after f) (seed : Fin E→Layout k) (i : Fin (E*2^(j+r))) : V :=
  after ((chart (rotor sp seed)).symm (i,⟨0,Nat.two_pow_pos j⟩))

theorem owner_at (seed : Fin E→Layout k) (room : j≤b)
    (opened : ∀u:P,start u=seed u.2 ((address k).symm u.1))
    (sameSlab : ∀u v:P,u.2=v.2→before u=before v) (u : P) :
    after u=owner s seed (chart (j:=j) (r:=r) (rotor s seed) u).1 := by
  let rows := chart (j := j) (r := r) (rotor s seed)
  let zeroLane : Fin (2^j) := ⟨0, Nat.two_pow_pos j⟩
  let home := rows.symm ((rows u).1, zeroLane)
  change after u = after home
  apply one_home s seed room opened sameSlab u home
  exact (congrArg Prod.fst (rows.apply_symm_apply ((rows u).1, zeroLane))).symm

end
end Hierarchy.DescentTerminalExteriorPackets

end OAI
