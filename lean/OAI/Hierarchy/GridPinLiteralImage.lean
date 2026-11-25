import OAI.Hierarchy.FactorPinIntervals
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Readback of the actual captured-source scatter for every input pin -/

namespace Hierarchy.GridPinLiteralImage
open FactorPinIntervals
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical

variable {T : Type} {S N d w z : ℕ}

/-- The native word loop writes one distinct destination per source row. -/
def writeRows (address : ℕ→ℕ) (source : ℕ→Word w) (m : Memory w) : ℕ→Memory w
  | 0 => m
  | n+1 => Function.update (writeRows address source m n) (address n) (source n)

theorem writeRows_congr (adr adr' : ℕ→ℕ) (src src' : ℕ→Word w) (m : Memory w) (n : ℕ)
    (whereAt : ∀ i<n, adr i=adr' i) (what : ∀ i<n,src i=src' i) :
    writeRows adr src m n=writeRows adr' src' m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [writeRows,writeRows,ih (fun i hi=>whereAt i (by omega)) (fun i hi=>what i (by omega)),
      whereAt n (by omega),what n (by omega)]

theorem untouched (addr : ℕ→ℕ) (src : ℕ→Word w) (m : Memory w) (n a : ℕ)
    (away : ∀ i<n, addr i≠a) : writeRows addr src m n a=m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [writeRows,Function.update_of_ne (away n (by omega)).symm]
    exact ih (fun i hi => away i (by omega))

theorem hit (addr : ℕ→ℕ) (src : ℕ→Word w) (m : Memory w) (n j : ℕ)
    (inside : j<n) (unique : ∀ i<n, addr i=addr j → i=j) :
    writeRows addr src m n (addr j)=src j := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases eqn : j=n
    · subst j; simp [writeRows]
    · have dif : addr j≠addr n := fun same => eqn (unique n (by omega) same.symm).symm
      rw [writeRows,Function.update_of_ne dif]
      exact ih (by omega) (fun i hi => unique i (by omega))

def headerOnly (P : Layout T S N d) (t : T) (i : Fin d) :=
  if hi : i.val<(P.header t).length then (P.header t)[i.val] else false

variable (P : Layout T S N d) (code : (T×Fin d) ↪ Fin z) (base low : ℕ)

def dest (i : ℕ) := if h : low+i<S then base+(code (P.address ⟨low+i,h⟩)).val else base

private theorem dest_eq {j : Fin S} {i : ℕ} (h : low+i=j.val) :
    dest P code base low i=base+(code (P.address j)).val := by
  have hi : low+i<S := by rw [h]; exact j.isLt
  simp [dest,h]

private theorem header_at_slot (j : Fin S) : headerOnly P (P.tick j) (P.slot j)=false := by
  have wide : ¬(P.slot j).val<(P.header (P.tick j)).length := by rw [P.slot_val rfl]; omega
  simp [headerOnly,wide]

theorem equals_literal (n : ℕ) (fit : low+n≤S) (src : ℕ→Word w) (m : Memory w)
    (init : ∀ t i, m (base+(code (t,i)).val)=((headerOnly P t i).toNat:Word w))
    (on : ∀ (i : ℕ) (hi : i<n), src i=((P.advice ⟨low+i,by omega⟩).toNat : Word w))
    (off : ∀ j : Fin S, (j.val<low ∨ low+n≤j.val) → P.advice j=false)
    (t : T) (i : Fin d) :
    writeRows (dest P code base low) src m n (base+(code (t,i)).val)=((P.literal t i).toNat:Word w) := by
  let pin := base+(code (t,i)).val
  have decode (a : ℕ) (ha : a<n) (eqn : dest P code base low a=pin) :
      P.address ⟨low+a,by omega⟩=(t,i) := by
    rw [dest_eq P code base low (j:=⟨low+a,by omega⟩) rfl] at eqn
    exact code.injective (Fin.ext (Nat.add_left_cancel eqn))
  by_cases has : ∃ j : Fin S, P.address j=(t,i)
  · obtain ⟨j,eqn⟩ := has
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eqn.symm
    rw [P.literal_slot]
    by_cases valid : low≤j.val ∧ j.val<low+n
    · let a := j.val-low
      have hin : a<n := by dsimp [a];omega
      have ix : low+a=j.val := by dsimp [a];omega
      have toAddr := dest_eq P code base low ix
      change writeRows (dest P code base low) src m n (base+(code (P.address j)).val)=_
      rw [←toAddr,hit _ _ _ _ a hin]
      · have h := on a hin
        simpa [ix] using h
      · intro b hb same
        change dest P code base low b=dest P code base low a at same
        have destSame := P.address.injective (decode b hb (same.trans toAddr))
        have equal : low+b=j.val := congrArg Fin.val destSame
        omega
    · rw [untouched,init,header_at_slot,off j (by omega)]
      intro a ha same
      have z := P.address.injective (decode a ha same)
      have eqn : low+a=j.val := congrArg Fin.val z
      omega
  · have away (a : ℕ) (ha : a<n) : dest P code base low a≠pin := fun eqn =>
      has ⟨_,decode a ha eqn⟩
    rw [untouched _ _ _ _ _ away,init]
    by_cases hi : i.val<(P.header t).length
    · simp [headerOnly,hi,P.literal_header t i hi]
    · have past : (P.inputBits t).length ≤ i.val-(P.header t).length := by
        by_contra! before
        let k : Fin (P.inputBits t).length := ⟨i.val-(P.header t).length,before⟩
        obtain ⟨ht,hs⟩ := P.slot_get t k
        apply has
        refine ⟨(P.inputBits t).get k,Prod.ext ht (Fin.ext ?_)⟩
        change (P.slot ((P.inputBits t).get k)).val=i.val
        rw [hs]
        dsimp [k]
        omega
      simp [Layout.literal,headerOnly,hi,List.getElem?_eq_none past]

end Hierarchy.GridPinLiteralImage

end OAI
