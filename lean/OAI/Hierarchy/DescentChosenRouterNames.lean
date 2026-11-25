import OAI.Hierarchy.DescentResetTreePrice
import OAI.Hierarchy.DescentOutputSlots
import OAI.Hierarchy.DescentRouterSlots

namespace OAI
/-! # Real dyadic base names and common physical contacts of a selected reset -/

namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentBaseProfile DescentRouterSlots
open scoped Classical BigOperators
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
variable {k Y : ℕ} (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k) (keys : Finset (V×ℕ))
variable (hub : V→Prop) (old : Bool→I→V×Block k)

/-- The identity of a paid device is a genuine unmarked nonhub dyadic base. -/
abbrev Good := {p : BaseId b // p∉validBases b keys ∧ ¬hub p.1}

def useRotor (i : I) : Prop := ∀s, baseOf b hk L (old s i)∉validBases b keys ∧ ¬hub (old s i).1

def base (i : {i // useRotor b hk L keys hub old i}) (s : Bool) : Good b keys hub :=
  ⟨baseOf b hk L (old s i.val),i.property s⟩

theorem fallback_iff (i : I) : ¬useRotor b hk L keys hub old i ↔
    i∈badEdgeSet b hk L (old false) (old true) keys ∨ hub (old false i).1 ∨ hub (old true i).1 := by
  simp [useRotor,badEdgeSet,validBases,Bool.forall_bool]
  tauto

abbrev Site := Good b keys hub ⊕ H
abbrev Public := (Good b keys hub × Fin Y) ⊕ H

def site : Public (Y:=Y) (H:=H) b keys hub → Site (H:=H) b keys hub := Sum.elim (Sum.inl ∘ Prod.fst) Sum.inr

variable (ends : Bool→A→Good b keys hub) (span : A→ℕ)
variable (room : ∀s g,(∑a : {a // ends s a=g},span a.val)≤Y)
/-- Each globally named reserved output socket has one physical base at
each end and a common number of slots on the two ends. -/
abbrev Reserve := Σ a : A,Fin (span a)

def slot (s : Bool) (j : Reserve span) : Good b keys hub × Fin Y :=
  let g := ends s j.1
  (g,outputSlot (fun a : {a // ends s a=g}=>span a.val) (room s g) ⟨⟨j.1,rfl⟩,j.2⟩)

private def fibres (s : Bool) : Reserve span ≃
    Σ g : Good b keys hub, Σ t : {a // ends s a=g},Fin (span t.val) where
  toFun q := ⟨ends s q.1,⟨q.1,rfl⟩,q.2⟩
  invFun q := ⟨q.2.1.val,q.2.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨g,⟨a,h⟩,k⟩;subst g;rfl

theorem slot_unique (s : Bool) : Function.Injective (slot b keys hub ends span room s) := by
  let render (z : Σ g : Good b keys hub, Σ t : {a // ends s a=g},Fin (span t.val)) :=
    (z.1,outputSlot (fun t : {a // ends s a=z.1}=>span t.val) (room s z.1) z.2)
  have inject : Function.Injective render := by
    rintro ⟨g,p⟩ ⟨g',p'⟩ h
    have same : g=g' := congrArg Prod.fst h
    subst g'
    exact congrArg (Sigma.mk g)
      (outputSlot_injective (fun t : {a // ends s a=g} => span t.val) (room s g) (congrArg Prod.snd h))
  exact inject.comp (fibres b keys hub ends span s).injective

variable (ticket : {i // useRotor b hk L keys hub old i}→Reserve span)
variable (anchored : ∀i s,ends s (ticket i).1=base b hk L keys hub old i s)
variable (row : Bool→V×Block k→Fin Y) (fallback : Bool→V×Block k→H)

def pub (s : Bool) (i : I) : Public (Y:=Y) (H:=H) b keys hub :=
  if paid : useRotor b hk L keys hub old i then .inl (base b hk L keys hub old ⟨i,paid⟩ s,row s (old s i))
  else .inr (fallback s (old s i))

abbrev Bad := {i : I // ¬useRotor b hk L keys hub old i}

def pair (i : Bad b hk L keys hub old) : H×H := (fallback false (old false i.val),fallback true (old true i.val))

/-- Only actual exceptional pairs become links. Noninteracting fallback
terminals create neither a cable nor a post-reset neighbour. -/
abbrev Seen := (Finset.univ.image (pair b hk L keys hub old fallback) : Finset (H×H))
abbrev Contact := Reserve span ⊕ Seen b hk L keys hub old fallback

def contact (i : I) : Contact b hk L keys hub old span fallback :=
  if paid : useRotor b hk L keys hub old i then .inl (ticket ⟨i,paid⟩)
  else .inr ⟨pair b hk L keys hub old fallback ⟨i,paid⟩,Finset.mem_image.mpr ⟨⟨i,paid⟩,Finset.mem_univ _,rfl⟩⟩

def owner (s : Bool) : Contact b hk L keys hub old span fallback → Site (H:=H) b keys hub
  | .inl c => .inl (ends s c.1)
  | .inr p => .inr (if s then p.val.2 else p.val.1)

include anchored in
omit [Fintype H] [Fintype A] in
theorem aligned (s : Bool) (i : I) :
    site b keys hub (pub b hk L keys hub old row fallback s i)=owner b hk L keys hub old ends span fallback s
      (contact b hk L keys hub old span ticket fallback i) := by
  by_cases paid : useRotor b hk L keys hub old i
  · simp [pub,contact,site,owner,paid,anchored]
  · cases s <;> simp [pub,contact,site,owner,pair,paid]

omit [Fintype H] [Fintype A] in
theorem in_good_iff (s : Bool) (i : I) :
    (∃g : Good b keys hub,owner b hk L keys hub old ends span fallback s
      (contact b hk L keys hub old span ticket fallback i)=.inl g) ↔ useRotor b hk L keys hub old i := by
  by_cases paid : useRotor b hk L keys hub old i <;> simp [contact,paid,owner]

def first (s : Bool) (g : Good b keys hub) :
    InputId (fun _ : Bool=>site (Y:=Y) (H:=H) b keys hub) s (.inl g) ↪ Fin Y where
  toFun v := match v with
    | ⟨.inl (_,r),_⟩ => r
    | ⟨.inr _,h⟩ => False.elim (by contradiction)
  inj' := by
    rintro ⟨⟨a,r⟩|t,h⟩ ⟨⟨a',r'⟩|t',h'⟩ same <;> simp [site] at h h' same ⊢; subst_vars; rfl

def last (s : Bool) (g : Good b keys hub) :
    LinkId (owner b hk L keys hub old ends span fallback) s (.inl g) ↪ Fin Y where
  toFun v := match v with
    | ⟨.inl c,_⟩ => (slot b keys hub ends span room s c).2
    | ⟨.inr _,h⟩ => False.elim (by contradiction)
  inj' := by
    rintro ⟨a|p,ha⟩ ⟨a'|p',hb⟩ eq
    · apply Subtype.ext
      apply congrArg Sum.inl
      apply slot_unique b keys hub ends span room s
      exact Prod.ext (Sum.inl.inj (ha.trans hb.symm)) eq
    · exact False.elim (by simp only [owner, Sum.inr_ne_inl] at hb)
    · exact False.elim (by simp only [owner, Sum.inr_ne_inl] at ha)
    · exact False.elim (by simp only [owner, Sum.inr_ne_inl] at ha)

omit [Fintype H] in
theorem fallback_root (s : Bool) (t : H) :
    Subsingleton (InputId (fun _ : Bool=>site (Y:=Y) (H:=H) b keys hub) s (.inr t)) := by
  constructor
  rintro ⟨⟨g,r⟩|t₁,h₁⟩ ⟨⟨g',r'⟩|t₂,h₂⟩ <;> simp [site] at h₁ h₂ ⊢; subst_vars; rfl

end
end Hierarchy.DescentChosenRouter

end OAI
