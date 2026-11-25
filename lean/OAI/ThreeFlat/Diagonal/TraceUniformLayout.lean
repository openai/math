import OAI.ThreeFlat.Diagonal.TraceUniformAddress
import OAI.ThreeFlat.Diagonal.TracePhysicalArrayLayout

namespace OAI
/-! # Public XOR offsets for the program-independent checker -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open LaneCursor
open TracePhysical (laneRow flatRow offset)
variable {F : Type*} {w p r k f S d lane low n c : ℕ}

/-- The extra program bits are placed in the row carried in the leading
coordinate of their copy ordinal. -/
def hiddenOwner (fits : S+f ≤ 2^(1+d)) : Fin (SharedCount w p r k d f) → Fin (2^d) :=
  Fin.addCases (TracePhysical.hiddenOwner fits) (fun c =>
    (finProdFinEquiv.symm c : Fin (2^d) × Fin ((1+6*p+k)*w)).1)

def owner (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d)) :
    BitSource (SharedCount w p r k d f) (S*w) → Fin (2^d)
  | .constant _ => v
  | .pin j => TracePhysical.headerOwner fits j
  | .hidden h => hiddenOwner fits h

private theorem owner_keep (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d))
    (z : BitSource (Fintype.card (TracePhysical.Shared w r f d)) (S*w)) :
    owner (p := p) (k := k) fits v (keepSource z) = TracePhysical.owner fits v z := by
  cases z <;> simp [owner, TracePhysical.owner, hiddenOwner, keepSource]

private theorem owner_copy (fits : S+f ≤ 2^(1+d)) (v u : Fin (2^d)) (j : Fin (1+6*p+k) × Fin w) :
    owner (r := r) (p := p) (k := k) fits v (.hidden (Fin.natAdd
      (Fintype.card (TracePhysical.Shared w r f d)) (copyOrdinal u j))) = u := by
  simp only [owner, hiddenOwner, copyOrdinal, Fin.addCases_right, Equiv.symm_apply_apply]

theorem reachable (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d)) (port : Port w p r k d) :
    TracePhysical.Reached v (owner fits v (addresses hw S f v port)) := by
  rcases port with a | ⟨b,j⟩
  · simpa only [addresses,owner_keep,TracePhysical.Reached] using TracePhysical.reachable hw fits v a
  · cases b with
    | false => simpa only [addresses, Bool.false_eq_true, ite_false, owner_copy] using TracePhysical.sameSite v
    | true =>
      simp only [addresses, ite_true]
      split
      · rw [owner_copy]
        exact TracePhysical.consecutive v _ (Or.inl rfl)
      · exact TracePhysical.sameSite v

def code (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d)) (port : Port w p r k d) :
    Fin (1+(d+d)) :=
  Fin.find (fun j => (owner fits v (addresses hw S f v port)).val ^^^ v.val = (offset d j).val)
    (reachable hw fits v port)

theorem reaches (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+d)) (v : Fin (2^d)) (port : Port w p r k d) :
    v.val = (owner fits v (addresses hw S f v port)).val ^^^ (offset d (code hw fits v port)).val := by
  have h := Fin.find_spec (reachable hw fits v port)
  change _ ^^^ _ = (offset d (code hw fits v port)).val at h
  rw [← h]
  simp

theorem laneOwner (fits : S+f ≤ 2^(1+(lane+low))) (v : Fin (2^(lane+low)))
    (z : BitSource (SharedCount w p r k (lane+low) f) (S*w)) :
    sourceRow (laneRow ∘ hiddenOwner fits) (laneRow ∘ TracePhysical.headerOwner fits) (laneRow v) z =
       laneRow (owner fits v z) := by cases z <;> rfl

/-- Reindex the actual flat enumeration of sites into high lane bits and low
bucket bits, retaining every assembled cell in its original position. -/
def indexedLayout {t b q P o : ℕ} (ht : t = 2^lane*2^low)
    (rows : Fin t → Fin c → TraceCircuit.Cell F n q) (inp : Fin t → Fin q → BitSource b P)
    (hidden : Fin b → Row lane low) (pins : Fin P → Row lane low)
    (off : Fin o → Row lane low) (base : Fin o) (hbase : (off base).val=0)
    (idx : Fin t → Fin q → Fin o) (ok : ∀ v j,
      v.cast ht = partner (sourceRow hidden pins (v.cast ht) (inp v j)) (off (idx v j))) :
    RowLayout (TraceCircuit.assemble rows inp) lane low o c := by
  subst t
  exact TraceCircuit.arrayLayout rows inp hidden pins off base hbase idx ok

theorem indexedLayout_pins {t b q P o : ℕ} (ht : t = 2^lane*2^low)
    (rows : Fin t → Fin c → TraceCircuit.Cell F n q) (inp : Fin t → Fin q → BitSource b P)
    (hidden : Fin b → Row lane low) (pins : Fin P → Row lane low)
    (off : Fin o → Row lane low) (base : Fin o) (hbase : (off base).val=0)
    (idx : Fin t → Fin q → Fin o) (ok : ∀ v j,
      v.cast ht = partner (sourceRow hidden pins (v.cast ht) (inp v j)) (off (idx v j))) :
    (indexedLayout ht rows inp hidden pins off base hbase idx ok).pinRow = pins := by
  subst t
  rfl

noncomputable def arrayLayout (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+(lane+low)))
    (rows : Fin (2^(lane+low)) → Fin c → TraceCircuit.Cell F n (Fintype.card (Port w p r k (lane+low)))) :
    RowLayout (TraceCircuit.assemble rows (fun v j => addresses hw S f v
      ((Fintype.equivFin (Port w p r k (lane+low))).symm j))) lane low
      (1+((lane+low)+(lane+low))) c :=
  indexedLayout (Nat.pow_add ..) rows _ (laneRow ∘ hiddenOwner fits)
    (laneRow ∘ TracePhysical.headerOwner fits) (laneRow ∘ offset (lane+low)) 0
    (TracePhysical.offset_zero _) (fun v j => code hw fits v ((Fintype.equivFin _).symm j)) (by
      intro v j
      change laneRow v = partner (sourceRow _ _ (laneRow v) _) _
      rw [laneOwner]
      apply Fin.ext
      exact reaches hw fits v ((Fintype.equivFin (Port w p r k (lane+low))).symm j))

theorem arrayLayout_pins (hw : 2 ≤ w+1) (fits : S+f ≤ 2^(1+(lane+low)))
    (rows : Fin (2^(lane+low)) → Fin c → TraceCircuit.Cell F n (Fintype.card (Port w p r k (lane+low)))) :
    (arrayLayout hw fits rows).pinRow = laneRow ∘ TracePhysical.headerOwner fits :=
  indexedLayout_pins ..

end ThreeFlat.Diagonal.TraceUniformRow

end OAI
