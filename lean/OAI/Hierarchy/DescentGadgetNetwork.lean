import OAI.Hierarchy.DescentSplitWires
import OAI.Hierarchy.DescentSixPartyGadget

namespace OAI
/-! # The selected physical motif network before absorbed wires are contracted -/

namespace Hierarchy.DescentSixParty.GadgetNetwork
open Computability.VPVNP Computability.VPVNP.WireTensor Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {I : Type} [Fintype I] {D : ℕ} {P : Type*} {bits : P → ℕ}
variable (N : Network D P bits) (pick : I × Fin 2 ↪ N.Edge)

def selected (e : N.Edge) : Option (I × Fin 2) :=
  if h : ∃ t,pick t=e then some h.choose else none

theorem selected_spec {e : N.Edge} {t : I × Fin 2} (h : selected N pick e=some t) : pick t=e := by
  unfold selected at h
  split at h
  next ex => cases Option.some.inj h;exact ex.choose_spec
  next => contradiction

@[simp] theorem selected_pick (t : I × Fin 2) : selected N pick (pick t)=some t := by
  have h : ∃ s,pick s=pick t := ⟨t,rfl⟩
  simp [selected]

abbrev Site := N.Site ⊕ (I × Fin 6)
abbrev Edge := N.Edge ⊕ ((I × Fin 2) ⊕ (I × Fin 8))

/-- The original cable is reused as the first arm when it is selected.
All untouched original cables retain both of their old endpoints. -/
def source : Edge (I:=I) N → Site (I:=I) N
  | .inl e => .inl (N.src e)
  | .inr (.inl t) => .inr (t.1,demandDst t.2)
  | .inr (.inr t) => .inr (t.1,supplySrc t.2)

def target : Edge (I:=I) N → Site (I:=I) N
  | .inl e => match selected N pick e with
    | none => .inl (N.dst e)
    | some t => .inr (t.1,demandSrc t.2)
  | .inr (.inl t) => .inl (N.dst (pick t))
  | .inr (.inr t) => .inr (t.1,supplyDst t.2)

def width (supply : I → Fin 8 → ℕ) : Edge (I:=I) N → ℕ
  | .inl e => N.width e
  | .inr (.inl t) => N.width (pick t)
  | .inr (.inr t) => supply t.1 t.2

def physical (supply : I → Fin 8 → ℕ) : Network D P bits where
  Site := Site (I:=I) N
  Edge := Edge (I:=I) N
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := source N
  dst := target N pick
  width := width N pick supply
  attach := Sum.inl ∘ N.attach
  position := Sum.elim N.position (fun t => N.position (N.src (pick (t.1,0))))
  in_ball := by
    rintro (v|t)
    · exact N.in_ball v
    · exact N.in_ball _

variable (sw : I → Fin 8 → ℕ)
local notation "M" => physical N pick sw

abbrev Local (v : (M).Site) := ∀ e : {e : (M).Edge // (M).src e=v ∨ (M).dst e=v},Fin ((M).width e.val) → Bool

abbrev Arms := (t : I × Fin 2) → Fin (N.width (pick t)) → Bool

private def restoreAt (head : N.Assignment) (arm : Arms N pick) (e : N.Edge) :
    (choice : Option (I × Fin 2)) → (selected N pick e = choice) → Fin (N.width e) → Bool
  | none, _ => head e
  | some t, found => fun j => arm t (Fin.cast (congrArg N.width (selected_spec N pick found).symm) j)

def restore (head : N.Assignment) (arm : Arms N pick) (e : N.Edge) : Fin (N.width e) → Bool :=
  restoreAt N pick head arm e (selected N pick e) rfl

private theorem restore_at (head : N.Assignment) (arm : Arms N pick) (e : N.Edge)
    (choice : Option (I × Fin 2)) (found : selected N pick e = choice) :
    restore N pick head arm e = restoreAt N pick head arm e choice found := by
  subst choice
  rfl

theorem restore_none (head : N.Assignment) (arm : Arms N pick) (e : N.Edge)
    (found : selected N pick e = none) : restore N pick head arm e = head e :=
  restore_at N pick head arm e none found

@[simp] theorem restore_pick (head : N.Assignment) (arm : Arms N pick) (t : I × Fin 2) :
    restore N pick head arm (pick t)=arm t :=
  restore_at N pick head arm (pick t) (some t) (selected_pick N pick t)

def oldRight (a : (M).Assignment) : N.Assignment :=
  restore N pick (fun e=>a (.inl e)) (fun t=>a (.inr (.inl t)))

def ends (a : (M).Assignment) : Ends N := (fun e=>a (.inl e),oldRight N pick sw a)

@[simp] theorem right_pick (a : (M).Assignment) (t : I × Fin 2) :
    oldRight N pick sw a (pick t)=a (.inr (.inl t)) := by
  exact restore_pick N pick _ _ t

private def targetWord (v : N.Site) (read : Local N pick sw (.inl v)) (e : N.Edge)
    (atDst : N.dst e = v) : (choice : Option (I × Fin 2)) →
      (selected N pick e = choice) → Fin (N.width e) → Bool
  | none, found => read ⟨.inl e, Or.inr (by simp [physical,target,found,atDst])⟩
  | some t, found => fun j => read ⟨.inr (.inl t), Or.inr (by
      change Sum.inl (N.dst (pick t)) = Sum.inl v
      rw [selected_spec N pick found,atDst])⟩
      (Fin.cast (congrArg N.width (selected_spec N pick found).symm) j)

private theorem targetWord_read (a : (M).Assignment) (v : N.Site) (e : N.Edge)
    (atDst : N.dst e = v) (choice : Option (I × Fin 2)) (found : selected N pick e = choice) :
    targetWord N pick sw v (fun i => a i.val) e atDst choice found =
      restoreAt N pick (fun i => a (.inl i)) (fun t => a (.inr (.inl t))) e choice found := by
  cases choice <;> rfl

def siteWord (v : N.Site) (read : Local N pick sw (.inl v))
    (e : {e : N.Edge // N.src e=v ∨ N.dst e=v}) : Fin (N.width e.val) → Bool :=
  if s : N.src e.val=v then read ⟨.inl e.val, Or.inl (congrArg Sum.inl s)⟩
  else targetWord N pick sw v read e.val (e.property.resolve_left s) (selected N pick e.val) rfl

private theorem siteWord_read (a : (M).Assignment) (v : N.Site)
    (e : {e : N.Edge // N.src e=v ∨ N.dst e=v}) :
    siteWord N pick sw v (fun i=>a i.val) e=
      if N.src e.val=v then (ends N pick sw a).1 e.val else (ends N pick sw a).2 e.val := by
  by_cases h : N.src e.val = v
  · have sourceRead : siteWord N pick sw v (fun i => a i.val) e =
        (ends N pick sw a).1 e.val := dite_eq_left h
    exact sourceRead.trans (ite_eq_left h).symm
  · calc
      siteWord N pick sw v (fun i => a i.val) e =
          targetWord N pick sw v (fun i => a i.val) e.val (e.property.resolve_left h)
            (selected N pick e.val) rfl := dite_eq_right h
      _ = (ends N pick sw a).2 e.val :=
        targetWord_read N pick sw a v e.val (e.property.resolve_left h) _ rfl
      _ = _ := (ite_eq_right h).symm

variable (dw : I → ℕ) (fit : ∀i s,N.width (pick (i,s))=dw i)
variable {F : Type*} [Field F]
abbrev Demand (i : I) := MotifBase.binaryWires (k:=F) demandSrc demandDst (fun _=>dw i)
abbrev Supply (i : I) := MotifBase.binaryWires (k:=F) supplySrc supplyDst (sw i)

def demandPorts (i : I) (j : Fin 6) (read : Local N pick sw (.inr (i,j))) :
    (Demand (F:=F) dw i).Basis j :=
  (fun s hj => Fin.cast (congrArg (2^·) (fit i s)) (bitsFin _ (read
     ⟨.inl (pick (i,s)),Or.inr (by simp [physical,target,hj])⟩)),
   fun s hj => Fin.cast (congrArg (2^·) (fit i s)) (bitsFin _ (read
     ⟨.inr (.inl (i,s)),Or.inl (by simp [physical,source,hj])⟩)))

def supplyPorts (i : I) (j : Fin 6) (read : Local N pick sw (.inr (i,j))) :
    (Supply (F:=F) sw i).Basis j :=
  (fun e hj => bitsFin _ (read ⟨.inr (.inr (i,e)),Or.inl (by simp [physical,source,hj])⟩),
   fun e hj => bitsFin _ (read ⟨.inr (.inr (i,e)),Or.inr (by simp [physical,target,hj])⟩))

def tables (old : N.Tables F) (L : ∀ i j,(Demand (F:=F) dw i).Basis j → (Supply (F:=F) sw i).Basis j → F) :
    (M).Tables F
  | .inl v,read,pins => old v (siteWord N pick sw v read) (fun t=>pins ⟨t.val,congrArg Sum.inl t.property⟩)
  | .inr (i,j),read,_ => L i j (demandPorts N pick sw dw fit i j read) (supplyPorts N pick sw i j read)

variable (T : N.Tables F) (L : ∀ i j,(Demand (F:=F) dw i).Basis j → (Supply (F:=F) sw i).Basis j → F)

theorem old_read (a : (M).Assignment) (pins : Ports bits) (v : N.Site) :
    (M).read (tables N pick sw dw fit T L) a pins (.inl v) =
      splitRead N T pins (ends N pick sw a) v := by
  have words : siteWord N pick sw v (fun i => a i.val) =
      (fun e : {e : N.Edge // N.src e=v ∨ N.dst e=v} =>
        if N.src e.val=v then (ends N pick sw a).1 e.val else (ends N pick sw a).2 e.val) :=
    funext (siteWord_read N pick sw a v)
  exact congrArg (fun read => T v read (fun t => pins t.val)) words

def supplyWords (a : (M).Assignment) (i : I) (e : Fin 8) : Fin (2^(sw i e)) :=
  bitsFin _ (a (.inr (.inr (i,e))))

theorem party_read (a : (M).Assignment) (pins : Ports bits) (i : I) (j : Fin 6) :
    (M).read (tables N pick sw dw fit T L) a pins (.inr (i,j)) =
      L i j (demandInput N pick dw fit (ends N pick sw a) i j)
        (edgeAssignment supplySrc supplyDst (supplyWords N pick sw a i) j) := by
  simp only [Network.read,tables,demandPorts,supplyPorts,ends,demandInput,right_pick,edgeAssignment,supplyWords]

end
end Hierarchy.DescentSixParty.GadgetNetwork

end OAI
