import OAI.ThreeFlat.Diagonal.CompressorNativeSweep
import OAI.ThreeFlat.Diagonal.CompressorNativeExpr
import OAI.ThreeFlat.Diagonal.CompressorTagScan

namespace OAI
/-! # Simulation of the chronological descriptor table by the physical word scan -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression RAM.DescriptorExpr
open scoped Fin.NatCast
variable {V A B : Type*} {w k d : ℕ}

theorem pick_map [DecidableEq A] [DecidableEq B] (encode : A ↪ B) (bad : List A)
    (fallback : A) (choices : List A) :
    Ordered.pick (bad.map encode) (encode fallback) (choices.map encode) =
      encode (Ordered.pick bad fallback choices) := by
  induction choices with
  | nil => rfl
  | cons a xs ih =>
    have hit : encode a ∈ bad.map encode ↔ a ∈ bad := by
      simp only [List.mem_map]
      exact ⟨fun ⟨b,h,e⟩ => encode.injective e ▸ h,fun h => ⟨a,h,rfl⟩⟩
    by_cases h : a ∈ bad <;> simp [Ordered.pick,hit,h,ih]

def Represents (atWord : V → Word w) (value : A → Word w) (m : Memory w) (table : V → A) : Prop :=
  ∀ v, m (atWord v).val = value (table v)

theorem represents_write [DecidableEq V] {atWord : V → Word w} (hinj : Function.Injective atWord)
    {value : A → Word w} {m : Memory w} {table : V → A}
    (ok : Represents atWord value m table) (v : V) (a : A) :
    Represents atWord value (writeMemory m (atWord v) (value a)) (Function.update table v a) := by
  intro x
  by_cases h : x=v
  · subst x
    simp [writeMemory]
  · have hn : (atWord x).val ≠ (atWord v).val := fun e => h (hinj (Fin.ext e))
    simp [writeMemory,hn,Function.update_of_ne h,ok x]

/-- Indexing the next address by adding the old list length is unnecessary:
the pointer is advanced in the same native modular arithmetic as the driver. -/
inductive Consecutive (atWord : V → Word w) : Word w → List V → Prop
  | nil (a) : Consecutive atWord a []
  | cons {v vs a} (head : atWord v = a) (tail : Consecutive atWord (a+1) vs) :
      Consecutive atWord a (v::vs)

theorem consecutive_of_get (atWord : V → Word w) (a : Word w) (xs : List V)
    (indexed : ∀ i : Fin xs.length, atWord (xs.get i) = a+(i.val : Word w)) :
    Consecutive atWord a xs := by
  induction xs generalizing a with
  | nil => exact .nil a
  | cons x xs ih =>
    apply Consecutive.cons
    · simpa using indexed 0
    · apply ih
      intro i
      simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using indexed i.succ

theorem sweep_scan [DecidableEq V] [DecidableEq A]
    (choices : List A) (fallback : A) (ban : V → (V → A) → List A)
    (atWord : V → Word w) (addresses : Function.Injective atWord) (value : A → Word w)
    (f : Word w → Memory w → Word w) (immutable : Memory w → Prop)
    (preserve : ∀ m v z, immutable m → immutable (writeMemory m (atWord v) z))
    (row : ∀ m table x, immutable m → Represents atWord value m table →
      f (atWord x) m = value (Ordered.pick (ban x table) fallback choices))
    (xs : List V) (a : Word w) (m : Memory w) (table : V → A)
    (next : Consecutive atWord a xs) (good : immutable m) (rep : Represents atWord value m table) :
    immutable (sweep f xs.length a m) ∧ Represents atWord value (sweep f xs.length a m)
      (Ordered.scan xs choices fallback ban table) := by
  induction next generalizing m table with
  | nil => exact ⟨good,rep⟩
  | @cons x xs a head tail ih =>
    subst a
    let z := Ordered.pick (ban x table) fallback choices
    have update := represents_write addresses rep x z
    have step := row m table x good rep
    change immutable (sweep f xs.length _ _) ∧ Represents _ _ (sweep f xs.length _ _) _
    rw [step]
    exact ih _ _ (preserve m x (value z) good) update

theorem color_val {G : SlotGraph V d} (x : V) (table : V → Fin (2*d+1))
    (nfit : 2*d+1 ≤ 2^w) (one : (1 : Word w) ≠ 0)
    (pub : Fin k → Word w) (m : Memory w) (p : Word w)
    (tab dst src : Term w k 1) (vertex : V → Word w)
    (pointer : p - tab.eval pub m (fun _ => p) = vertex x)
    (lookup : ∀ v, m (tab.eval pub m (fun _ => p) + vertex v).val = ((table v).val : Word w))
    (outgoing : ∀ i : Fin d, m (dst.eval pub m (fun _ => p) + vertex x*(d:Word w) + (i.val:Word w)).val =
      vertex (G.target (x,i)).1)
    (incoming : ∀ i : Fin d, m (src.eval pub m (fun _ => p) + vertex x*(d:Word w) + (i.val:Word w)).val =
      vertex (G.target.symm (x,i)).1) :
    (colorRow d tab dst src).eval pub m (fun _ => p) =
      ((Ordered.pick (Ordered.colorBan G x table) 0 (List.ofFn (Equiv.refl (Fin (2*d+1))))).val : Word w) := by
  let embed : Fin (2*d+1) ↪ Word w := ⟨fun i => i.castLE nfit,fun _ _ h => Fin.ext (congrArg (fun n : Word w => n.val) h)⟩
  have e (i : Fin (2*d+1)) : (i.val : Word w) = embed i :=
    Fin.ext (Nat.mod_eq_of_lt (i.isLt.trans_le nfit))
  have eqBans :
      (colorBans d tab dst src (.binary .sub (.result 0) tab)).map (fun z => z.eval pub m (fun _ => p)) =
        (Ordered.colorBan G x table).map embed := by
    simp [colorBans,Ordered.colorBan,Ordered.directions,List.map_append,List.map_ofFn,Function.comp_def,eval_readRow,eval_readSlot,Term.eval,BinaryOp.eval,pointer,outgoing,incoming,
      lookup,adjacent,e]
  rw [colorRow,eval_firstFree one,eqBans]
  convert pick_map embed (Ordered.colorBan G x table) 0 (List.ofFn (Equiv.refl (Fin (2*d+1)))) using 1
  · have ez : embed 0 = 0 := Fin.ext (show (0 : Fin (2*d+1)).val = (0 : Word w).val by
      simp only [Fin.val_zero])
    simp [List.map_ofFn,Function.comp_def,e,ez]
  · exact e _

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
