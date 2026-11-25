import OAI.ThreeFlat.Diagonal.RefreshChoiceNative
import OAI.ThreeFlat.Diagonal.RefreshSourceFrame
import OAI.ThreeFlat.Diagonal.RefreshDenseAddress
import OAI.ThreeFlat.RAM.SweepSegment

namespace OAI
/-! # Refresh preparation publishes the descriptor of every true motif -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorScan
open RefreshDemandRows RefreshTies CompressorPacking.Native MotifIntegerChoice
open scoped Fin.CommRing
noncomputable section

variable {W v a t k : ℕ} (current : Word W) (m : Memory W)
set_option quotPrecheck false
local notation "N" => fun i=>(m i).val

theorem header_val (off : ℕ) (cap : (m current.val).val+off<2^W) :
    (headerWord m current off).val=info N current off := by
  change (m (m current.val+(off:Word W)).val).val=_
  rw [←Fin.cast_val_eq_self (m current.val),←Nat.cast_add,Fin.val_cast_of_lt cap]

/-- Row-addressed output for a finite typed table. No default cell can be
read inside the scan bounds. -/
def tableWord {A : Type} {n : ℕ} (e : A ≃ Fin n) (base : ℕ) (word : A → Word W) (i : ℕ) : Word W :=
  if h : i-base<n then word (e.symm ⟨i-base,h⟩) else 0

theorem tableWord_at {A : Type} {n : ℕ} (e : A ≃ Fin n) (base : ℕ) (word : A → Word W) (a : A) :
    tableWord e base word (base+(e a).val)=word a := by
  have cancel : base+(e a).val-base=(e a).val := by omega
  simp [tableWord,cancel,(e a).isLt]

abbrev choices : Block v t × Fin 3 ≃ Fin (3*(v*2^t)) :=
  RefreshStageLayout.descriptorEntries (m:=mPort a) (h:=0) (pad:=0)

def descriptorWord (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (w : SlotImage.RefreshInput v a t → ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size : Fin (k+1) → ℕ) (q : Block v t × Fin 3) : ℕ :=
  let d := fun e=>SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) q.1 e)
  let j := tileNumber d base
  if q.2.val=0 then score d base j else if q.2.val=1 then j.val else size j

theorem choice_run
    (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)) (C : SlotImage.Columns) (split stride : ℕ)
    (w : SlotImage.RefreshInput v a t → ℕ) (s : Source current m G C split w)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) (size : Fin (k+1) → ℕ)
    (destination : info N current 2=stride) (length : info N current 18=3*(v*2^t))
    (space : stride+3*(v*2^t)<2^W) (laneFit : 2^t<2^W) (portFit : mPort a≤2^W) (rowsFit : k+1≤2^W)
    (tileFit : ∀ z j i,sentinel (fun e => SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm)
      z e))+base j i<2^W)
    (protect : ∀ i,sourceCell current.val (m current.val).val C split (v*mPort a*(mPort a*2^t)) i →
      i<stride ∨ stride+3*(v*2^t)≤ i) :
    (Pipeline.scan current 2 18 (closed (choiceWords current base size))).run m =
      fillSegment stride (3*(v*2^t))
        (tableWord (choices (a:=a)) stride (fun q=>(descriptorWord G w base size q:Word W))) m := by
  have cap := s.headerBound
  have len := (header_val current m 18 (by omega)).trans length
  have start := (header_val current m 2 (by omega)).trans destination
  let scan := fun x mem' => (closed (choiceWords current base size)).eval (Fin.elim0 : Fin 0 → Word W) mem' (fun _=>x)
  let book := tableWord (choices (a:=a)) stride (fun q=>(descriptorWord G w base size q:Word W))
  change sweep scan _ _ m=fillSegment _ _ book m
  rw [len]
  calc
    _ = fillSegment (headerWord m current 2).val (3*(v*2^t)) book m := by
      apply sweep_segment scan stride (stride+3*(v*2^t)) m book _ _ _ m start.ge (by omega) space (fun _ _=>rfl)
      intro x lb ub m' frame
      let i : Fin (3*(v*2^t)) := ⟨x.val-stride,by omega⟩
      let q := (choices (a:=a)).symm i
      have id : (choices (a:=a) q).val=i.val := congrArg Fin.val ((choices (a:=a)).apply_symm_apply i)
      have pos : x.val=stride+(choices (a:=a) q).val := by dsimp only [i] at id; omega
      have row : (choices (a:=a) q).val=blockId q.1*3+q.2.val :=
        RefreshStageLayout.descriptor_index q.1 q.2
      have src := s.frame m' (fun j hj=>frame j (protect j hj))
      have ptr := frame _ (protect current.val (Or.inl rfl))
      have addr : info (fun j=>(m' j).val) current 2=stride := by
        dsimp only [info]
        rw [ptr,frame _ (protect _ (Or.inr (Or.inl ⟨by omega,by omega⟩)))]
        exact destination
      have atWord : x.val=info (fun j=>(m' j).val) current 2+blockId q.1*3+q.2.val := by omega
      have actual := choice_native current m' (fun _=>x) G C split w src q.1 q.2 base size atWord
        laneFit portFit rowsFit (tileFit q.1)
      simpa only [book,pos,tableWord_at,scan,descriptorWord] using actual
    _ = _ := by rw [start]

end

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
