import OAI.ThreeFlat.Diagonal.NavigationScalar
import OAI.ThreeFlat.Diagonal.TraceBitHeaderOffsets
import OAI.ThreeFlat.Diagonal.TraceMaskDictionary
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Publishing both public mask arrays for the first native trace leaf -/

namespace Hierarchy.TraceReceiverMaskBanks

open ThreeFlat Diagonal LaneCursor LaneCursor.RowLayout
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.EffectStream RAM.PhysicalProcedure
open scoped Fin.CommRing

variable {W : ℕ}

abbrev count (lane low : ℕ) := 1+((lane+low)+(lane+low))

def rowOffset (lane low : ℕ) (i : Fin (count lane low)) : Row lane low :=
  TracePhysical.laneRow (TracePhysical.offset (lane+low) i)

def sparse (lane low base : ℕ) : List (Record W) :=
  List.ofFn fun i => ((base+(rowOffset lane low i).val : ℕ),
    (firstIndex (rowOffset lane low) i).val)

def dense (lane low base : ℕ) : List (Record W) :=
  List.ofFn fun i : Fin (count lane low) =>
    ((base+i.val : ℕ),(rowOffset lane low i).val)

/-- Each public address and value is an immediate of the native writer. -/
def stores : List (Record W) → Procedure W
  | [] => NavigationPass.skip
  | s::xs => (NavigationPass.start s.1 s.2).seq (stores xs)

private theorem stores_exec (xs : List (Record W)) (m : Memory W) :
    (stores xs).Exec m (after m (events xs)) (3*xs.length+1) := by
  induction xs generalizing m with
  | nil => exact Procedure.Spec.exec NavigationPass.skip_spec m trivial
  | cons x xs ih =>
    have first : (NavigationPass.start x.1 x.2).Exec m (writeMemory m x.1 x.2) 3 := Procedure.Spec.exec (NavigationPass.start_spec x.1 x.2) m trivial
    have next : ((NavigationPass.start x.1 x.2).seq (stores xs)).Exec m
        (after (writeMemory m x.1 x.2) (events xs)) (3+(3*xs.length+1)) :=
      Procedure.Exec.then first (ih (writeMemory m x.1 x.2))
    intro P R K M pc reg pub exit rom data cfg init entry eqn
    simpa only [stores,List.length_cons,Nat.mul_succ,
      show after m (events (x::xs))=after (writeMemory m x.1 x.2) (events xs) by rfl,
      show 3 + (3 * xs.length + 1) = 3 * xs.length + 3 + 1 by omega] using
      next M pc reg pub exit rom data cfg init entry eqn

def program (W lane low dictBase masks : ℕ) : Procedure W :=
  (stores (sparse lane low dictBase)).seq (stores (dense lane low masks))

def image (lane low dictBase masks : ℕ) (m : Memory W) : Memory W :=
  after (after m (events (sparse lane low dictBase))) (events (dense lane low masks))

theorem run (lane low dictBase masks : ℕ) (m : Memory W) :
    (program W lane low dictBase masks).Exec m (image lane low dictBase masks m)
      (6*count lane low+2) := by
  have h : (program W lane low dictBase masks).Exec m (image lane low dictBase masks m)
      ((3*(sparse (W:=W) lane low dictBase).length+1)+(3*(dense (W:=W) lane low masks).length+1)) :=
    Procedure.Exec.then (stores_exec (sparse lane low dictBase) m)
    (stores_exec (dense lane low masks) (after m (events (sparse lane low dictBase))))
  intro P R K M pc reg pub exit rom data cfg init entry eqn
  simpa only [sparse,dense,List.length_ofFn,
    show 3*count lane low+1+(3*count lane low+1)=6*count lane low+2 by omega] using
    h M pc reg pub exit rom data cfg init entry eqn

private theorem stores_size (xs : List (Record W)) :
    (stores xs).labels=3*xs.length+1 ∧ (stores xs).registers=2*xs.length+1 ∧
      (stores xs).slots=0 := by
  induction xs with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons x xs ih =>
    change 3+(stores xs).labels=3*(xs.length+1)+1 ∧
      2+(stores xs).registers=2*(xs.length+1)+1 ∧ 0+(stores xs).slots=0
    rw [ih.1,ih.2.1,ih.2.2]
    exact ⟨by omega,by omega,rfl⟩

theorem size (lane low dictBase masks : ℕ) :
    (program W lane low dictBase masks).labels = 6*count lane low+2 ∧
    (program W lane low dictBase masks).registers = 4*count lane low+2 ∧
    (program W lane low dictBase masks).slots = 0 := by
  have h := stores_size (sparse (W:=W) lane low dictBase)
  have g := stores_size (dense (W:=W) lane low masks)
  simp only [sparse,dense,List.length_ofFn] at h g
  simp only [program,sparse,dense,Procedure.seq,h.1,h.2.1,h.2.2,g.1,g.2.1,g.2.2]
  exact ⟨by omega,by omega,trivial⟩

private theorem unchanged (xs : List (Record W)) (m : Memory W) (x : ℕ)
    (away : ∀ z∈xs, z.1.val≠x) : after m (events xs) x=m x := by
  apply after_at _ _ _ _ _ (Or.inl rfl)
  intro z hz hit
  exact (away z hz hit).elim

private theorem dense_frame (lane low masks : ℕ) (m : Memory W) (x : ℕ)
    (fit : masks+count lane low≤2^W) (away : x < masks ∨ masks+count lane low≤x) :
    after m (events (dense lane low masks)) x = m x := by
  apply unchanged
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  have hi := i.isLt
  change ((masks+i.val : ℕ) : Word W).val≠x
  rw [Fin.val_cast_of_lt (by omega)]
  omega

theorem frame (lane low dictBase masks : ℕ) (m : Memory W) (x : ℕ)
    (dfit : dictBase+2^lane*2^low≤2^W) (mfit : masks+count lane low≤2^W)
    (awayD : x<dictBase ∨ dictBase+2^lane*2^low≤x)
    (awayM : x < masks ∨ masks+count lane low≤x) : image lane low dictBase masks m x=m x := by
  rw [image,dense_frame _ _ _ _ _ mfit awayM]
  apply unchanged
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  have hi := (rowOffset lane low i).isLt
  change ((dictBase+(rowOffset lane low i).val : ℕ) : Word W).val≠x
  rw [Fin.val_cast_of_lt (by omega)]
  omega

private theorem dense_read (lane low masks : ℕ) (m : Memory W)
    (fit : masks+count lane low≤2^W) (word : 2^lane*2^low ≤ 2^W)
    (i : Fin (count lane low)) :
    (after m (events (dense lane low masks)) (masks+i.val)).val = (rowOffset lane low i).val := by
  have castAddr (j : Fin (count lane low)) : ((masks+j.val : ℕ) : Word W).val=masks+j.val :=
    Fin.val_cast_of_lt (by have := j.isLt; omega)
  let addr := fun j : Fin (count lane low) => ((masks+j.val : ℕ) : Word W)
  let val := fun j : Fin (count lane low) => ((rowOffset lane low j).val : Word W)
  have inj : Function.Injective addr := by
    intro i j eq
    have pos := congrArg Fin.val eq
    change ((masks+i.val : ℕ) : Word W).val=((masks+j.val : ℕ) : Word W).val at pos
    rw [castAddr,castAddr] at pos
    exact Fin.ext (by omega)
  have h := congrArg Fin.val (after_ofFn addr val m inj i)
  change (after m (events (dense lane low masks)) ((masks+i.val : ℕ) : Word W).val).val =
    (((rowOffset lane low i).val : Word W)).val at h
  rwa [castAddr, Fin.val_cast_of_lt ((rowOffset lane low i).isLt.trans_le word)] at h

/-- At the trace word width, adjacent banks fit in one high scratch sector.
The caller may choose the beginning of any free sector in the stated range. -/
theorem sector_room {w lane low high : ℕ} (large : 7≤w) (depth : lane+low≤2*w+1)
    (atMost : high≤30*2^(32*w)) :
    high+2^lane*2^low+count lane low ≤ high+2^(32*w) ∧
    high+2^lane*2^low+count lane low < 2^(64*w) := by
  let e:=32*w-1
  have hspan : 2^lane*2^low ≤ 2^e := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  have ht : count lane low ≤ 2^e := by
    have h : count lane low ≤ e := by dsimp [count,e]; omega
    exact h.trans Nat.lt_two_pow_self.le
  have size : 2^e+2^e=2^(32*w) := by
    rw [show 32*w=e+1 by dsimp [e]; omega,pow_succ]
    omega
  have top : 32*2^(32*w)<2^(64*w) := by
    change 2^5*2^(32*w)<2^(64*w)
    rw [←pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  omega

section Trace

variable {F : Type*} [Fintype F] [CommRing F] {w p S f lane low : ℕ}
    (hF : Fintype.card F≤2^w) (hw : 3≤w+1) (hp : p≤2^(w+1)) (base : ℕ)
    (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+(lane+low)))
local notation "P" => TraceBitHeader.layout hF hw hp base st hs hf r k fit
local notation "R" => TraceBitHeader.rawLayout hF hw hp base st hs hf r k fit
local notation "N" => TraceBitHeader.network hF hw hp base st hs hf r k (lane+low)

/-- The two concrete lookup hypotheses used by the first four-word atom. -/
theorem readouts (dictBase masks : ℕ) (m : Memory W)
    (dfit : dictBase+2^lane*2^low≤2^W) (mfit : masks+count lane low≤2^W)
    (apart : dictBase+2^lane*2^low ≤ masks ∨ masks+count lane low≤dictBase) :
    let o := image lane low dictBase masks m
    (∀ a : Occurrence N, (o (dictBase+((P).offset ((P).code a)).val)).val=((P).code a).val) ∧
    ∀ i, (o (masks+i.val)).val=((P).offset i).val := by
  have raw := TraceBitHeader.rawLayout_offset hF hw hp base st hs hf r k fit
  have hdict : sparse (W:=W) lane low dictBase = (R).dictionary dictBase := by
    simp only [sparse, RowLayout.dictionary, raw]
    rfl
  constructor
  · intro a
    let i := (R).code a
    have loc : (P).offset ((P).code a)=(R).offset i := first_eq (R).offset i
    rw [loc]
    have idx := ((R).offset i).isLt
    have out : dictBase+((R).offset i).val < masks ∨ masks+count lane low≤dictBase+((R).offset i).val := by
      omega
    rw [image,dense_frame _ _ _ _ _ mfit out,hdict,(R).read_dictionary _ _ dfit i]
    have codeFit : (firstIndex (R).offset i).val < count lane low := (firstIndex (R).offset i).isLt
    exact Fin.val_cast_of_lt (by omega)
  · intro i
    change (after _ (events (dense lane low masks)) (masks+i.val)).val=_
    simpa only [TraceBitHeader.layout_offset,rowOffset] using
      (dense_read lane low masks (after m (events (sparse lane low dictBase))) mfit (by omega) i)

end Trace

end Hierarchy.TraceReceiverMaskBanks

end OAI
