import OAI.Hierarchy.DescentMeasuredHeaderRAM
import OAI.Hierarchy.DescentPaddedEstimatorRows

namespace OAI
/-! # Exact zero extension across the variable genuine population of a public reset canvas -/
namespace Hierarchy.DescentPackedRectangle.Canvas
open DescentGL DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open scoped Classical Fin.CommRing
noncomputable section
variable {H P Δ D k : ℕ} (hosts : H≤P) (ports : Δ≤D)
local notation "R" => Rows H k Δ
local notation "Q" => Rows P k D

private abbrev publicOrder (P k D : ℕ) : Rows P k D ≃ Fin (P*(k+1+D)) :=
  (rowOrd P k D).trans (finCongr (Nat.mul_add P (k+1) D).symm)

def liftRow (t : R) : Q := match t with
  | .inl (v,j)=>.inl (v.castLE hosts,j)
  | .inr (v,j)=>.inr (v.castLE hosts,j.castLE ports)

theorem lift_ord (t:R) :
    publicOrder P k D (liftRow hosts ports t)=widen (m:=k) hosts ports (rowOrd H k Δ t) := by
  rcases t with ⟨v,j⟩|⟨v,j⟩ <;> apply Fin.ext <;>
    simp [liftRow,publicOrder,widen,rowOrd,DescentPackedExchange.slot,finCongr,
      finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_assoc,Nat.add_comm]

def extendedPort (next : Port H Δ→Option (Fin H)) (t : Port P D) : Option (Fin P) :=
  if h:t.1.val<H ∧ t.2.val<Δ then (next (⟨t.1.val,h.1⟩,⟨t.2.val,h.2⟩)).map (Fin.castLE hosts) else none

@[simp] theorem port_at (next : Port H Δ→Option (Fin H)) (v:Fin H) (j:Fin Δ) :
    extendedPort (D:=D) hosts next (v.castLE hosts,j.castLE ports)=(next (v,j)).map (Fin.castLE hosts) := by
  simp [extendedPort,v.isLt,j.isLt]

def liveHost (t : Q) := (owner t).val<H

/-- Every named live row retains the old value. All other rows are exactly the padding sentinel. -/
theorem extend_eq {α : Type} (blank : α) (x : R→α) (y : Q→α)
    (same : ∀t,y (liftRow hosts ports t)=x t)
    (ghost : ∀t,(¬∃s,liftRow hosts ports s=t)→y t=blank) (t : Q) :
    y t=padded (widen (m:=k) hosts ports) (x∘(rowOrd H k Δ).symm) blank (publicOrder P k D t) := by
  by_cases hit:∃s,liftRow hosts ports s=t
  · obtain ⟨s,rfl⟩:=hit
    rw [same,lift_ord,padded_at]
    simp
  · refine (ghost t hit).trans (padded_else _ _ blank _ ?_).symm
    rintro ⟨i,e⟩
    obtain ⟨s,rfl⟩:=(rowOrd H k Δ).surjective i
    exact hit ⟨s,(publicOrder P k D).injective ((lift_ord hosts ports s).trans e)⟩

theorem seen {α : Type} (blank : α) (x : R→α) (y : Q→α)
    (same : ∀t,y (liftRow hosts ports t)=x t)
    (unlisted : ∀(v:Fin P) (j:Fin D),Δ≤j.val→y (.inr (v,j))=blank) (t : Q) :
    (if liveHost (H:=H) t then y t else blank)=
      padded (widen (m:=k) hosts ports) (x∘(rowOrd H k Δ).symm) blank (publicOrder P k D t) := by
  refine extend_eq hosts ports blank x (fun q => if liveHost (H:=H) q then y q else blank) ?_ ?_ t
  · intro s
    have live : liveHost (H:=H) (liftRow hosts ports s) := by
      rcases s with ⟨v,j⟩|⟨v,j⟩ <;> exact v.isLt
    exact (ite_eq_left live).trans (same s)
  · intro s absent
    split
    · rename_i yes
      rcases s with ⟨v,j⟩|⟨v,j⟩
      · have live:v.val<H:=yes
        exact (absent ⟨.inl (⟨_,live⟩,j),rfl⟩).elim
      · have live:v.val<H:=yes
        by_cases small : j.val<Δ
        · exact (absent ⟨.inr (⟨_,live⟩,⟨_,small⟩),rfl⟩).elim
        · exact unlisted v j (by omega)
    · rfl

variable (depth : Fin H→ℕ) (dp : Fin P→ℕ) (actual : ∀v,dp (v.castLE hosts)=depth v)
    (next : Port H Δ→Option (Fin H))
local notation "edges" => extendedPort (D:=D) hosts next

include actual in
theorem depth_at (t : R) :
    realDepth dp edges (liftRow hosts ports t)=realDepth depth next t := by
  rcases t with ⟨v,j⟩|⟨v,j⟩
  · simp [liftRow,realDepth,actual]
  · simp only [liftRow,realDepth,port_at]
    cases next (v,j) <;> simp [actual]

include actual in
theorem gain_at (f B K : ℕ) (t : R) :
    realGain dp edges f B K (liftRow hosts ports t)=realGain depth next f B K t := by
  rcases t with ⟨v,j⟩|⟨v,j⟩
  · simp [liftRow,realGain,actual]
  · simp only [liftRow,realGain,port_at]
    cases next (v,j) <;> rfl

include actual in
theorem load_at (site : Fin H→Bits k→ℕ) (flow : Port H Δ→Bits k→ℕ)
    (sp : Fin P→Bits k→ℕ) (fp : Port P D→Bits k→ℕ)
    (rs : ∀v,sp (v.castLE hosts)=site v) (rf : ∀v j,fp (v.castLE hosts,j.castLE ports)=flow (v,j))
    (t : R) : realLoad dp edges sp fp (liftRow hosts ports t)=realLoad depth next site flow t := by
  rcases t with ⟨v,j⟩|⟨v,j⟩
  · simp [liftRow,realLoad,actual,rs]
  · simp only [liftRow,realLoad,port_at]
    cases next (v,j) <;> simp [rf]

theorem load_zero (site : Fin P→Bits k→ℕ) (flow : Port P D→Bits k→ℕ)
    (blank : ∀v,H≤v.val→site v=fun _=>0) (t : Q) (ghost : ¬∃s,liftRow hosts ports s=t) :
    realLoad dp edges site flow t=fun _=>0 := by
  rcases t with ⟨v,j⟩|⟨v,j⟩
  · have stop:¬v.val<H:=fun low=>ghost ⟨.inl (⟨_,low⟩,j),rfl⟩
    simp [realLoad,blank v (by omega)]
  · have stop:¬(v.val<H ∧ j.val<Δ):=fun live=>ghost ⟨.inr (⟨_,live.1⟩,⟨_,live.2⟩),rfl⟩
    simp [realLoad,extendedPort,stop]

end
end Hierarchy.DescentPackedRectangle.Canvas

end OAI
