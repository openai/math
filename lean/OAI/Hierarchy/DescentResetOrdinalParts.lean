import OAI.Hierarchy.DescentResetOrdinalDigits
import OAI.Hierarchy.DescentResetCableSlots

namespace OAI
/-! # The original componentwise priority of every installed reset parent -/
namespace Hierarchy.DescentResetCableSlots
open DescentRouterSlots DescentChosenRouter DescentContacts DescentCommonHost DescentHostDirectory
open DescentResetWireTags DescentMixedRouter DescentResetOrdinalDigits
open scoped Classical
noncomputable section
variable {V F A I H : Type} [Fintype V] [DecidableEq V] [Fintype F] [Fintype A] [Fintype I] [Field H]
variable {k n h C₀ bits u U one : ℕ} (P : Placement V I F A k (2^n)) (vertex : V↪Fin U)
variable (code : F↪V×Endpoint (2^n))
variable (valid : ∀f,(code f).2.1.1≤k ∧ (code f).2.1.2<2^(code f).2.1.1)

def goodLayout (U k : ℕ) := Layout.product (.digit U) (.digit (2^k))
def termLayout (U k Y : ℕ) := Layout.product (.digit U) (.product (.digit (2^(k+1))) (.digit (Y+1)))

def baseDigits (good : P.Good) : (goodLayout U k).Value :=
  (vertex good.val.1,Fin.castLE (Nat.pow_le_pow_right (by decide) (P.depth _)) good.val.2)

def terminalDigits (t : F) : (termLayout U k (2^n)).Value :=
  (vertex (code t).1,interval k ⟨(code t).2.1,mem_codes (valid t).1 (valid t).2⟩,optional (code t).2.2)

theorem baseDigits_value (good : P.Good) :
    (goodLayout U k).place (baseDigits P vertex good)=base P vertex good := rfl
omit [Fintype V] [DecidableEq V] [Fintype F] in
theorem terminalDigits_value (t : F) :
    (termLayout U k (2^n)).place (terminalDigits vertex code valid t)=terminal vertex code valid t := rfl

variable (Ht : ℕ) (depth : ∀s t,(P.fallbackBook s t).height≤Ht)
def directLayout (U k Y Ht : ℕ) := Layout.append
  (.product (goodLayout U k) (.digit Y)) (.product (termLayout U k Y) (.digit (2^Ht)))

/-- The paid contact reads its true left column. The fallback contact reads
its actual left terminal and the registered code of its incident leaf. -/
def directDigits (c : P.Contact) : (directLayout U k (2^n) Ht).Value :=
  match leftSocket P c with
  | .inl a=>let row:=paidSlot P a; .inl (baseDigits P vertex row.1,row.2)
  | .inr a=>.inr (terminalDigits vertex code valid a.1,leaf P Ht depth false a.1 a.2)

theorem directDigits_value (c : P.Contact) :
    (directLayout U k (2^n) Ht).place (directDigits P vertex code valid Ht depth c)=contact P vertex code valid Ht depth c := by
  cases c <;> rfl

variable (G : NonlinearExpanders.Graph n h)
local notation "localCap" => max (Fintype.card (Computability.BorderVNP.Crossing.Network.Edge (DescentCommonPalette.rotor G))) (2^(Ht+1))
variable (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=H) (C₀:=C₀) (u:=u) P G hw pay) (D : ℕ)
local notation "sel" => selected P G hw pay hardware
local notation "bank" => network G hw u P.contact P.input P.site P.owner P.align sel D

def kernelLayout (U k Y cap : ℕ) := Layout.product
  (.product (.digit 2) (.append (goodLayout U k) (termLayout U k Y))) (.digit cap)

def siteDigits : P.Site→ (Layout.append (goodLayout U k) (termLayout U k (2^n))).Value
  | .inl x=>.inl (baseDigits P vertex x)
  | .inr x=>.inr (terminalDigits vertex code valid x)

/-- The side and original good or exceptional terminal are separate inputs.
The last digit is the instruction in the template at that terminal. -/
def kernelDigits (v : Bool×P.Site) (e : (device G hw u P.contact P.input P.site P.owner P.align (D:=D) (sel v.1 v.2)).Edge) :
    (kernelLayout U k (2^n) localCap).Value :=
  ((finTwoEquiv.symm v.1,siteDigits P vertex code valid v.2),privateWire P Ht depth G hw pay hardware D v e)

def originalLayout (N U k Y Ht cap : ℕ) := Layout.append
  (.product (.digit 2) (.digit N)) (.append (termLayout U k Y)
    (.append (directLayout U k Y Ht) (kernelLayout U k Y cap)))
local notation "ordinalLayout" => originalLayout one U k (2^n) Ht localCap

def originParts (old : I↪Fin one) : ((Bool×I) ⊕ (F ⊕ (bank).Edge))→ (ordinalLayout).Value
  | .inl row => .inl (finTwoEquiv.symm row.1,old row.2)
  | .inr (.inl trunk) => .inr (.inl (terminalDigits vertex code valid trunk))
  | .inr (.inr (.inl link)) => .inr (.inr (.inl (directDigits P vertex code valid Ht depth link)))
  | .inr (.inr (.inr ⟨whereAt,e⟩)) => .inr (.inr (.inr (kernelDigits P vertex code valid Ht depth G hw pay hardware D whereAt e)))

local notation "parts" => originParts P vertex code valid Ht depth G hw pay hardware D
local notation "placed" => complete P vertex code valid Ht depth G hw pay hardware D

theorem originParts_value (old : I↪Fin one) (p : ((Bool×I) ⊕ (F ⊕ (bank).Edge))) :
    (ordinalLayout).place (parts old p)=placed old p := by
  rcases p with stem|trunk|link|⟨⟨s,root⟩,e⟩
  · rfl
  · rfl
  · cases link <;> rfl
  · cases root <;> rfl

theorem originParts_before (old : I↪Fin one) (p q : ((Bool×I) ⊕ (F ⊕ (bank).Edge))) :
    (ordinalLayout).before (parts old p) (parts old q) ↔ placed old p<placed old q := by
  rw [Layout.before_iff,originParts_value,originParts_value]
  exact ⟨fun h => h, fun h => h⟩

end
end Hierarchy.DescentResetCableSlots

end OAI
