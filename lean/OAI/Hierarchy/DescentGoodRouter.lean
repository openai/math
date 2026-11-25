import OAI.Hierarchy.DescentNamedRotor
import OAI.Hierarchy.DescentRouterSlots

namespace OAI
/-! # The configured good-base rotor on the actual coarse bank slots -/

namespace Hierarchy.DescentGoodRouter
open Computability.BorderVNP.Crossing DescentRouterSlots DescentNamedContact DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
variable (s : Bool) (w : W) {n h bits C₀ : ℕ} (G : NonlinearExpanders.Graph n h) {hw : 0<bits} {pay : ℝ}
variable (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "wt" => fun _ : I=>u
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "slot" => DescentNetworkSubstitution.Slot B (s,w)
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)
local notation "src" => (fun e : Item contact owner s w => first (root contact input site owner s w align e))
local notation "dst" => (fun e : Item contact owner s w => last (link contact owner s w e))
variable (P : BaseCircuit K G C₀ bits u hw
  (fun e : Item contact owner s w => first (root contact input site owner s w align e))
  (fun e : Item contact owner s w => last (link contact owner s w e)) pay)
local notation "M" => Physical.namedRotor G P D

def position (q : slot) : Physical.Pin (2^n) := Sum.elim (fun r=>(first r,false)) (fun c=>(last c,true))
  (names D contact input site owner wt s w q)

omit [Fintype R] in
private theorem position_injective : Function.Injective (position D u contact input site owner s w first last) := by
  intro a b same
  apply (names D contact input site owner wt s w).injective
  generalize ax : names D contact input site owner wt s w a = x
  generalize bx : names D contact input site owner wt s w b = y
  unfold position at same
  rw [ax,bx] at same
  rcases x with r|c <;> rcases y with t|k <;> simp_all

def words (p : Ports lens) : Ports (Physical.rawBits src dst u) :=
  Physical.rawPins (sourceWord D contact input site owner wt s w align p)
    (targetWord D contact input site owner wt s w p)

omit [Fintype R] in
private theorem local_words : DescentLocalAdapters.Local M
    (position D u contact input site owner s w first last) lens
    (words D u contact input site owner align s w first last) := by
  have fibre_ext {E J : Type} [Fintype E] [Fintype J] (label : E → J) (j : J)
      (a b : E → Fin u → Bool) (h : ∀ e, label e = j → a e = b e) :
      (labels label (fun _ => u)).symm a j = (labels label (fun _ => u)).symm b j := by
    have rows : (fun e : Fibre label j => a e.val) = (fun e : Fibre label j => b e.val) :=
      funext fun e => h e.val e.property
    let encode : (Fibre label j → Fin u → Bool) → (Fin (width label (fun _ => u) j) → Bool) :=
      (DescentContactTree.Physical.concat (fun _ : Fibre label j => u)).invFun
    with_unfolding_all exact congrArg encode rows
  intro v x y agree pin atv
  rcases pin with ⟨r,(_|_)⟩
  · apply fibre_ext src r (sourceWord D contact input site owner wt s w align x)
      (sourceWord D contact input site owner wt s w align y)
    intro e he
    let q := rootSlot D contact input site owner wt s w (root contact input site owner s w align e)
    have placed : position D u contact input site owner s w first last q = (r,false) := by
      simpa only [q,position,names_root,Sum.elim_inl] using
        congrArg (fun t : Fin (2^n) => (t,false)) he
    have keep := agree q ((congrArg (Physical.namedRotor G P D).attach placed).trans atv)
    unfold sourceWord
    rw [keep]
  · apply fibre_ext dst r (targetWord D contact input site owner wt s w x)
      (targetWord D contact input site owner wt s w y)
    intro e he
    let q := linkSlot D contact input site owner wt s w (link contact owner s w e)
    have placed : position D u contact input site owner s w first last q = (r,true) := by
      simpa only [q,position,names_link,Sum.elim_inr] using
        congrArg (fun t : Fin (2^n) => (t,true)) he
    have keep := agree q ((congrArg (Physical.namedRotor G P D).attach placed).trans atv)
    unfold targetWord
    rw [keep]


def device : Network D slot lens := DescentLocalAdapters.graph M (position D u contact input site owner s w first last) lens

def tables : (device D u contact input site owner align s w G first last P).Tables K :=
  DescentLocalAdapters.tables M (position D u contact input site owner s w first last) lens
    (Physical.namedTables G P D) (words D u contact input site owner align s w first last)

omit [Fintype R] in
theorem value (x : Bool→DescentContactTree.Physical.Row wt) (z : DescentContactTree.Physical.Row wt) :
    (device D u contact input site owner align s w G first last P).value
      (tables D u contact input site owner align s w G first last P)
      (DescentRouterBank.feed D contact input site owner wt x z s w)=
      if ∀i,owner s (contact i)=w → x s i=z i then 1 else 0 := by
  let feed := DescentRouterBank.feed D contact input site owner wt x z s w
  have transfer := DescentLocalAdapters.value M (position D u contact input site owner s w first last)
    lens (Physical.namedTables G P D) (words D u contact input site owner align s w first last)
    (local_words D u contact input site owner align s w G first last P) feed
  refine transfer.trans ?_
  refine (Physical.named_words G P (D := D)
    (sourceWord D contact input site owner wt s w align feed)
    (targetWord D contact input site owner wt s w feed)).trans ?_
  exact if_congr (word_agreement D contact input site owner wt s w align x z) rfl rfl

theorem degree (v : (device D u contact input site owner align s w G first last P).Site) :
    (device D u contact input site owner align s w G first last P).bitDegree v≤3 :=
  (DescentLocalAdapters.degree _ _ _ (position_injective D u contact input site owner s w first last) v).trans
    (Physical.named_degree G P v)

omit [Fintype R] in
theorem wires :
    ((∑ e,(device D u contact input site owner align s w G first last P).width e : ℕ):ℝ)≤
      21*((2*h+4)*(2*h*C₀+2):ℕ)*pay :=
  (Nat.cast_le.mpr (Nat.le_add_right _ _)).trans (Physical.named_price (D:=D) G P)

end
end Hierarchy.DescentGoodRouter

end OAI
