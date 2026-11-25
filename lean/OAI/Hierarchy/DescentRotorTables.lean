import OAI.ThreeFlat.CloudRestriction
import OAI.ThreeFlat.PortTileRepeat

namespace OAI
/-! # Fixed-table configurable rotors and their bundle powers -/

namespace Hierarchy.DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits Expander
open scoped BigOperators Classical
noncomputable section

variable {Y : ℕ}
local notation "V" => Fin Y
local notation "D" => demandGraph V

/-- Only the edge from a row to its configured image carries its data word. All
other edges have singleton alphabets, including unused loops and parallel ports. -/
def demandWidth (π : Equiv.Perm V) (w : ℕ) (p : V × V) :=
  if π p.1 = p.2 then w else 0

private def encodeWord (π : Equiv.Perm V) (w : ℕ) (p : V × V) (x : Fin (2^w)) :
    Fin (2^demandWidth π w p) :=
  if onPath : π p.1=p.2 then Fin.cast (by simp [demandWidth,onPath]) x
  else ⟨0,Nat.two_pow_pos _⟩

private theorem encodeWord_eq (π : Equiv.Perm V) (w : ℕ) (p : V × V) (x y : Fin (2^w)) :
    encodeWord π w p x = encodeWord π w p y ↔ (π p.1=p.2 → x=y) := by
  by_cases hit : π p.1=p.2 <;> simp [encodeWord,hit]

private def rowState (π : Equiv.Perm V) (w : ℕ) (v : V) (x y : Fin (2^w)) :
    (D).State (fun p => Fin (2^demandWidth π w p)) v :=
  fun p => encodeWord π w p.val.1 (if p.val.2 then y else x)

private theorem row_wiring (F : Type*) [Field F] (π : Equiv.Perm V) (w u : ℕ)
    (x y : V → Fin u → Fin (2^w)) :
    (D).wiring (K:=F) (fun p => Fin u → Fin (2^demandWidth π w p))
      (fun v port k => rowState π w v (x v k) (y v k) port) =
    if ∀ v, x v=y (π v) then 1 else 0 := by
  unfold PortGraph.wiring
  apply ite_congr ?_ (fun _ => rfl) (fun _ => rfl)
  apply propext
  constructor
  · intro all v
    funext k
    exact ((encodeWord_eq π w (v,π v) _ _).1 (congrFun (all (v,π v)) k)) rfl
  · rintro all ⟨v,z⟩
    funext k
    apply (encodeWord_eq π w (v,z) _ _).2
    intro hit
    change π v=z at hit
    change x v k=y z k
    rw [←hit]
    exact congrFun (all v) k

/-- One fixed list of local tables realizes a permutation on a given port host,
simultaneously at every bundle power. Each site reads only its own two rows, and
the shared sum is over one state per physical host edge. -/
def Configures (F : Type*) [Field F] (c : V → V → ℕ) (C w : ℕ) (π : Equiv.Perm V) : Prop :=
  ∃ tab : (v : V) → Fin (2^w) → Fin (2^w) →
      (supplyGraph c).State (fun _ => Fin (2^(C*w))) v → F,
    ∀ (u : ℕ) (x y : V → Fin u → Fin (2^w)),
      (supplyGraph c).contraction (A:=fun _ => Fin u → Fin (2^(C*w)))
        (fun v state => ∏ k, tab v (x v k) (y v k) (fun p => state p k)) =
        if ∀ v, x v=y (π v) then 1 else 0

/-- The ordinary tensor restrictions on a covered host give its rotor tables.
The width and the host are chosen before the permutation or its bundle power. -/
theorem configured_of_covers [NeZero Y] {F : Type*} [Field F] {c : V → V → ℕ} {C : ℕ}
    (covers : CloudCovers F c C) :
    ∃ threshold : ℕ, ∀ w ≥ threshold, ∀ π : Equiv.Perm V, Configures F c C w π := by
  classical
  obtain ⟨threshold,all⟩ := covers
  refine ⟨threshold,fun w hw π => ?_⟩
  have rows (v : V) : (∑ j : V, demandWidth π w (v,j)) ≤ 3*w := by
    simp [demandWidth]; omega
  have cols (z : V) : (∑ i : V, demandWidth π w (i,z)) ≤ 3*w := by
    have hit (i : V) : π i=z ↔ i=π.symm z := π.eq_symm_apply.symm
    simp [demandWidth,hit]; omega
  have res := all w hw (fun i j => demandWidth π w (i,j)) rows cols
  obtain ⟨M,tile⟩ := exists_repeat_port_tile D (supplyGraph c)
    (fun p => Fin (2^demandWidth π w p)) (fun _ => Fin (2^(C*w))) res
  refine ⟨fun v x y => M v (rowState π w v x y),fun u x y => ?_⟩
  let z : (v : V) → (D).State (fun p => Fin u → Fin (2^demandWidth π w p)) v := fun v port k => rowState π w v (x v k) (y v k) port
  have here := tile u z
  rw [← row_wiring F π w u x y]
  rw [PortGraph.contraction_eq_wiring]
  exact here.symm

end
end Hierarchy.DescentRotor

end OAI
