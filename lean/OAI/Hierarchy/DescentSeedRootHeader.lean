import OAI.Hierarchy.DescentSeedChoiceBits
import OAI.Hierarchy.DescentSeedRootJoinWords
import OAI.Hierarchy.DescentSeedTokenNumbers
import OAI.Hierarchy.DescentSeedRootRows
import OAI.ThreeFlat.Diagonal.TraceBanks
import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.Computability.VPVNP.RAMMemory

namespace OAI
/-! # Static initial-memory wires for the physical seed census and graph -/
namespace Hierarchy.DescentSeedRoot
open Hierarchy.DescentInitialHost
open ThreeFlat Routing Catalyst Diagonal TraceBanks
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)

abbrev Tag := Vertex X ⊕ (Cable X ⊕ Old X)
abbrev rows := rowCount X
def words (R : ℕ) := (R*rows X)*8

/-- Sites, wires and census rows occupy separate contiguous portions of a block. -/
def rowIndex : Tag X ≃ Fin (rows X) :=
  ((Fintype.equivFin _).sumCongr (((Fintype.equivFin _).sumCongr (Fintype.equivFin _)).trans
    finSumFinEquiv)).trans finSumFinEquiv

def address (R : ℕ) : ((Fin R × Tag X) × Fin 8) ≃ Fin (words X R) :=
  ((((Equiv.refl _).prodCongr (rowIndex X)).trans finProdFinEquiv).prodCongr (Equiv.refl _)).trans
    finProdFinEquiv

omit [Field F] in
theorem census_address {R : ℕ} (j : Fin R) (v : Old X) (q : Fin 8) :
    (address X R ((j,.inr (.inr v)),q)).val = q.val+censusBase X j v := rfl

omit [Field F] in
theorem census_pointer {R r : ℕ} {J : Type} [Fintype J] (digits : Fin R≃J×Fin (2^r))
    (j : Fin R) (v : Old X) (q : Fin 8) :
    (address X R ((j,.inr (.inr v)),q)).val=q.val+vertexWords X digits j (.inl v) 7 := rfl

variable {R s r : ℕ} {J : Type} [Fintype J] (digits : Fin R≃J×Fin (2^r))

def sourceWord (j : Fin R) (tag : Tag X) (q : Fin 8) :
    (Fin R × (Σ v : Old X,LocalPattern X v)) ⊕ ℕ :=
  match tag with
  | .inl v => .inr (vertexWords X digits j v q)
  | .inr (.inl e) => .inr (cableWords X s j e q)
  | .inr (.inr v) => match lookup X v q with
    | some pat => .inl (j,⟨v,pat⟩)
    | none => .inr 0

def wordAt (w : ℕ) (c : (initialGroup X R s).Choice) (i : Fin (words X R)) : Word w :=
  let a := (address X R).symm i
  ((sourceWord X (s:=s) digits a.1.1 a.1.2 a.2).elim (selected X c) id : ℕ)

def base (w : ℕ) (c : (initialGroup X R s).Choice) (a : ℕ) : Word w :=
  if h : a<words X R then wordAt X digits w c ⟨a,h⟩ else 0

theorem initial_read (w : ℕ) (c : (initialGroup X R s).Choice)
    (j : Fin R) (tag : Tag X) (q : Fin 8) :
    initialMemory (words X R) (base X digits w c) (address X R ((j,tag),q)).val =
      (((sourceWord X (s:=s) digits j tag q).elim (selected X c) id : ℕ) : Word w) := by
  simp [initialMemory,base,wordAt,(address X R ((j,tag),q)).isLt]

theorem siteID_read (w : ℕ) (c : (initialGroup X R s).Choice) (j : Fin R) (v : Vertex X) :
    initialMemory (words X R) (base X digits w c) (address X R ((j,.inl v),1)).val =
      ((siteOrder X c ⟨j,v⟩).val : Word w) := by
  rw [initial_read,siteOrder_val]
  rfl

theorem cableID_read (w : ℕ) (c : (initialGroup X R s).Choice) (j : Fin R) (e : Cable X) :
    initialMemory (words X R) (base X digits w c) (address X R ((j,.inr (.inl e)),1)).val =
      ((cableOrder X c ⟨j,e⟩).val : Word w) := by
  rw [initial_read,cableOrder_val]
  rfl

theorem census_read (w : ℕ) (c : (initialGroup X R s).Choice)
    (j : Fin R) (v : Old X) (pat : LocalPattern X v) :
    initialMemory (words X R) (base X digits w c)
      (address X R ((j,.inr (.inr v)),code X pat)).val = ((c j (.inl v) pat).val : Word w) := by
  rw [initial_read]
  simp [sourceWord,selected]

def headerPin (w : ℕ) (z : Fin (words X R) × Fin (w+1)) : Select X R s ⊕ Bool :=
  let a:=(address X R).symm z.1
  match sourceWord X (s:=s) digits a.1.1 a.1.2 a.2 with
  | .inr n => .inr (TraceWords.bits (wide (n : Word w)) z.2)
  | .inl key =>
      if h : z.2.val < min w (digitsNeeded s) then
        .inl (key,⟨z.2.val,(Nat.lt_min.mp h).2⟩)
      else .inr false

theorem agrees (w : ℕ) (c : (initialGroup X R s).Choice) (z : Fin (words X R) × Fin (w+1)) :
    (headerPin X (s:=s) digits w z).elim (selectBit X w c) id =
      TraceWords.bits (wide (base X digits w c z.1.val)) z.2 := by
  classical
  have hz := z.1.isLt
  simp only [headerPin,base,dite_eq_left hz,wordAt]
  split
  · rename_i n hkey
    rw [hkey]
    simp only [Sum.elim_inr,id_eq]
  · rename_i key hkey
    rw [hkey]
    dsimp only [Sum.elim_inl, TraceWords.bits, wide]
    split
    · rfl
    · rename_i hi
      dsimp
      apply Eq.symm
      apply Nat.testBit_lt_two_pow
      have low : ((selected X c key : Word w).val) < 2^min w (digitsNeeded s) := by
        by_cases ord : w ≤ digitsNeeded s
        · rw [Nat.min_eq_left ord]
          exact (selected X c key : Word w).isLt
        rw [Nat.min_eq_right (Nat.le_of_not_ge ord)]
        exact (Nat.mod_le _ _).trans_lt
          (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (c key.1 (.inl key.2.1) key.2.2).isLt)
            (Nat.lt_log2_self (n:=s)))
      exact low.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))

/-- Embed the private count slots into the common external/selector/paid alphabet. -/
theorem root_header {E C P : Type*} (w : ℕ) (c : (initialGroup X R s).Choice)
    (inject : Select X R s → C) (choice : C→Bool)
    (chosen : ∀ q,choice (inject q)=selectBit X w c q) (external : E→Bool) (paid : P→Bool) :
    let pin (z : Fin (words X R) × Fin (w+1)) :
        (E ⊕ (C ⊕ P)) ⊕ Bool := (headerPin X (s:=s) digits w z).map
            (fun q=>Sum.inr (Sum.inl (inject q))) id
    (fun z=>(pin z).elim (Sum.elim external (Sum.elim choice paid)) id) =
      (fun z=>TraceWords.bits (wide (base X digits w c z.1.val)) z.2) := by
  funext z
  rw [← agrees X digits w c z]
  cases h : headerPin X (s:=s) digits w z with
  | inl q => simpa only [h,Sum.map_inl,Sum.elim_inl,Sum.elim_inr] using chosen q
  | inr b => simp only [h,Sum.map_inr,Sum.elim_inr,id_eq]

/-- The next physical header word carries the exact selected seed site count.
The original graph and histogram rows keep their same addresses. Prefix can be
the actual raw header even when a malformed selector supplied its counts. -/
def countedBase (R w : ℕ) (initial : Fin (words X R)→Word w) : ℕ→Word w :=
  joinWords initial (fun _ : Fin 1 => (R*Fintype.card (Vertex X):ℕ))

def countPins {K : Type*} (R w : ℕ) (literal : Bool→K) (pins : Fin (words X R)×Fin (w+1)→K) :=
  joinPins pins (fun z : Fin 1×Fin (w+1)=>literal (TraceWords.bits
    (wide ((R*Fintype.card (Vertex X):ℕ):Word w)) z.2))

omit [Field F] in
theorem countPins_read {K : Type*} (R w : ℕ) (initial : Fin (words X R)→Word w)
    (literal : Bool→K) (emit : K→Bool) (lit : ∀ b,emit (literal b)=b)
    (pins : Fin (words X R)×Fin (w+1)→K) (read : ∀z,emit (pins z)=TraceWords.bits (wide (initial z.1)) z.2)
    (z : Fin (words X R+1)×Fin (w+1)) :
    emit (countPins X R w literal pins z)=TraceWords.bits (wide (countedBase X R w initial z.1.val)) z.2 :=
  join_agrees emit initial (fun _ : Fin 1=>(R*Fintype.card (Vertex X):ℕ)) pins _
    read (fun _t=>lit _) z

theorem siteCount_read (w : ℕ) (c : (initialGroup X R s).Choice) (initial : Fin (words X R)→Word w) :
    initialMemory (words X R+1) (countedBase X R w initial) (words X R)=
      (Fintype.card ((initialGroup X R s).state c).graph.Site : Word w) := by
  rw [initialSiteCard]
  simpa only [Fin.val_zero,Nat.add_zero,countedBase] using
    join_right initial (fun _ : Fin 1=>((R*Fintype.card (Vertex X):ℕ):Word w)) (0 : Fin 1)

theorem counted_initial_read (w : ℕ) (c : (initialGroup X R s).Choice) (j : Fin R) (tag : Tag X) (q : Fin 8) :
    initialMemory (words X R+1) (countedBase X R w (wordAt X digits w c)) (address X R ((j,tag),q)).val=
      ((sourceWord X (s:=s) digits j tag q).elim (selected X c) id : ℕ) := by
  rw [countedBase,join_left]
  simp [wordAt]

theorem census_exact (w : ℕ) (hw : s<2^w) (c : (initialGroup X R s).Choice)
    (j : Fin R) (v : Old X) (pat : LocalPattern X v) :
    (initialMemory (words X R) (base X digits w c)
      (address X R ((j,.inr (.inr v)),code X pat)).val).val = (c j (.inl v) pat).val := by
  rw [census_read]
  exact Nat.mod_eq_of_lt ((Nat.le_of_lt_succ (c j (.inl v) pat).isLt).trans_lt hw)

theorem words_bound (R : ℕ) : words X R ≤ 160*R*(X.size+1) := by
  have cost := («initialize» X).2.1
  change Fintype.card (Vertex X)+Fintype.card (Cable X)+Fintype.card (Port p X.width) ≤
    10*(X.size+1) at cost
  have part : Fintype.card (Old X) ≤ Fintype.card (Vertex X) :=
    Fintype.card_le_of_embedding ⟨Sum.inl,Sum.inl_injective⟩
  have h : rows X≤20*(X.size+1) := by unfold rows rowCount;omega
  unfold words
  calc
    _ ≤ (R*(20*(X.size+1)))*8 := Nat.mul_le_mul_right 8 (Nat.mul_le_mul_left R h)
    _ = _ := by ring


end
end Hierarchy.DescentSeedRoot

end OAI
