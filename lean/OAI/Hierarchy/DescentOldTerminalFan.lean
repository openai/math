import OAI.Hierarchy.DescentTrunkWorld
import OAI.Hierarchy.DescentResetQuantum
import OAI.Hierarchy.DescentSharedRows
import OAI.Hierarchy.DescentFineGoodLeaf
import OAI.Hierarchy.DescentInstalledNames

namespace OAI
/-! # Decode actual paid and exceptional public sockets into the same grouped old tensor -/

namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentContacts DescentFineTerminals DescentResetAttachments Computability.BorderVNP.Crossing
open scoped Classical BigOperators
open private label_injective from OAI.Hierarchy.DescentBadVolume
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k n : ℕ}

def goodAddress (b : V→ℕ) (keys : Finset (V×ℕ)) (hub : V→Prop) (p : Good b keys hub×Fin (2^n)) :
    V×Endpoint (2^n) := (p.1.val.1,((b p.1.val.1,p.1.val.2.val),some p.2))

theorem goodAddress_injective (b : V→ℕ) (keys : Finset (V×ℕ)) (hub : V→Prop) :
    Function.Injective (goodAddress (n:=n) b keys hub) := by
  intro p q same
  apply Prod.ext
  · apply Subtype.ext
    apply label_injective b
    exact congrArg (fun z : V×Endpoint (2^n) => (z.1,z.2.1.2)) same
  · exact Option.some.inj (congrArg (fun z : V×Endpoint (2^n)=>z.2.2) same)

variable (P : Placement V I H A k (2^n)) (code : H↪V×Endpoint (2^n))
def publicAddress : P.Public→V×Endpoint (2^n) := Sum.elim (goodAddress P.b P.keys P.hub) code
def mode (e : I) : Bool := decide (useRotor P.b P.depth P.L P.keys P.hub P.old e)
variable (paidName : ∀s i (h : useRotor P.b P.depth P.L P.keys P.hub P.old i),
    code (P.fall s (P.old s i)) =
      goodAddress P.b P.keys P.hub (base P.b P.depth P.L P.keys P.hub P.old ⟨i,h⟩ s,P.row s (P.old s i)))

include paidName in
theorem public_read (s : Bool) (i : I) :
    publicAddress P code (P.input s i)=code (P.fall s (P.old s i)) := by
  by_cases h : useRotor P.b P.depth P.L P.keys P.hub P.old i
  · simpa only [Placement.input,pub,dite_eq_left h,publicAddress,Sum.elim_inl] using (paidName s i h).symm
  · simp only [Placement.input,pub,dite_eq_right h,publicAddress,Sum.elim_inr]

include paidName in
theorem shared_receive (s : Bool) (i j : I) (eq : P.input s i=P.input s j) :
    P.fall s (P.old s i)=P.fall s (P.old s j) := by
  apply code.injective
  exact (public_read P code paidName s i).symm.trans
    ((congrArg (publicAddress P code) eq).trans (public_read P code paidName s j))

include paidName in
theorem shared_send (s : Bool) (i j : I) (eq : P.fall s (P.old s i)=P.fall s (P.old s j))
    (modeEq : mode P i=mode P j) : P.input s i=P.input s j := by
  by_cases hi : useRotor P.b P.depth P.L P.keys P.hub P.old i
  · have hj : useRotor P.b P.depth P.L P.keys P.hub P.old j := by simpa [mode,hi] using modeEq.symm
    simp only [Placement.input,pub,dite_eq_left hi,dite_eq_left hj,Sum.inl.injEq]
    apply goodAddress_injective P.b P.keys P.hub
    exact (paidName s i hi).symm.trans ((congrArg code eq).trans (paidName s j hj))
  · have hj : ¬useRotor P.b P.depth P.L P.keys P.hub P.old j := by simpa [mode,hi] using modeEq.symm
    simpa only [Placement.input,pub,dite_eq_right hi,dite_eq_right hj] using congrArg Sum.inr eq

end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentFineTerminals
open DescentGL DescentColonies DescentContacts DescentChosenRouter
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k n B f g Δ : ℕ}
local notation "nativeGap" => (32*Nat.clog 2 (2*Δ))
variable (near : V→Finset V) (weight : V→Block k→ℕ) (room : ∀v x,weight v x≤B)
variable (traffic : V→V→Block k→ℝ) (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k)
variable {K : ℕ} (hub : V→Bool) (enough : 2^n≤2^f) (rows : Bool→V×Block k→Fin (2^n))
local notation "keys" => resetKeys near Δ f B K weight traffic b hk L
local notation "mark" => fun v=>hub v=true
local notation "wt" => rearrangedLoad weight L
local notation "lim" => fun v i=>room v (Equiv.symm (rearrange L) i)
local notation "chosenRow" => sharedRow (D:=nativeGap) near wt lim b hk L keys mark enough rows
local notation "terminalAt" => terminal (D:=nativeGap) (f:=f) (g:=g) near wt lim b hub L chosenRow

theorem actual_good_name (s : Bool) (o : V×Block k) (ok : paid b hk L keys mark o) :
    (terminalAt s o).val=goodAddress b keys mark (⟨baseOf b hk L o,ok⟩,rows s o) := by
  have same := unflagged_leaf (K:=K) near weight room traffic b hk L o ok.1
  have ordinary : hub o.1=false := by cases eq : hub o.1 <;> simp_all [paid]
  simp [terminal,name,ordinary,same,shared_of_paid near wt lim b hk L keys mark enough rows ok,
    goodAddress,baseOf,layout_id]

theorem actual_side (common : ∀o,rows true o=rows false o) (o : V×Block k) :
    terminalAt true o=terminalAt false o := by
  apply Subtype.ext
  simp [terminal,name,sharedRow,oldRow,common]

end
end Hierarchy.DescentFineTerminals

end OAI
