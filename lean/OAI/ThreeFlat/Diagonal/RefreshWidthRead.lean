import OAI.ThreeFlat.Diagonal.RefreshWidthWriter

namespace OAI
/-! # Semantics of the refresh width ROM on the physical array -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows RefreshTies CompressorPacking.Native
open MotifIntegerChoice
open scoped Classical BigOperators
noncomputable section

variable {a t v h k W n : ℕ}
variable (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
variable (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs

private theorem externalWidth_read (C : Columns (Formula n)) (remaining block : Formula n) (z : Block v t)
    (s : Fin (mPort a)) {w : Address' v a t → ℕ} (stored : Stored G (C.map V) mem w)
    (hr : V remaining = 2^t) (hb : V block = blockId z) :
    V (externalWidth C remaining block s) = ∑ i, w (z,i,s) := by
  rw [externalWidth,totals_value,List.map_map]
  simp only [← List.ofFn_id,List.map_ofFn,Function.comp_def,List.sum_ofFn,demand_value,hr,hb,
    demand_read G stored,addr,Bool.false_eq_true,ite_false,id_eq]

def numberedWidth {m : ℕ} (s : Fin m) (slot : ℕ) (external : Fin m → ℕ)
    (sparse : Fin m → Fin h → ℕ) : ℕ :=
  if slot=0 then external s else if hi : slot-1<h then sparse s ⟨slot-1,hi⟩ else 0

/-- Exact output on port `s` comprises its concatenation, its numbered
sparse arcs in row order, and the trailing zero widths. -/
theorem generateWidth_value (C : Columns (Formula n)) (remaining idx counts : Formula n) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ)
    (w : Address' v a t → ℕ) (stored : Stored G (C.map V) mem w)
    (e : LiveSlot (Fin v) (BitWord t) (mPort a) (1+h+pad)) (hr : V remaining = 2^t) (hi : V idx = nextIndex e) :
    let z := (e.1.1.1,e.2)
    let s := fun j => w (addr (arrival G (tagOrdinal a).symm) z j)
    let j := tileNumber s base
    let r := score s base j
    V (generateWidth C remaining idx counts pad stride base size bits pool) =
      numberedWidth e.1.1.2 e.1.2.val (fun s => ∑ i, w (z,i,s))
        (fun port slot => r*bits j+∑ b : Fin (size j), mem (V counts+blockId z*stride+b.val)*pool j b port slot) := by
  dsimp only
  let z := (e.1.1.1,e.2)
  let p := cursor (mPort a) (1+h+pad) remaining idx
  let s := fun i => w (addr (arrival G (tagOrdinal a).symm) z i)
  let j := tileNumber s base
  let choice := refreshChoice C remaining p.block base
  let start := plus counts (.op .mul p.block (.lit stride))
  obtain ⟨hb,hp,hs⟩ := cursor_read e W data mem vs remaining idx hr hi
  change V p.block = blockId z at hb
  change V p.port = _ at hp
  change V p.slot = _ at hs
  have value := refreshChoice_value G W data mem vs C remaining p.block z w stored hr hb base
  have fst : V choice.1 = score s base j := congrArg Prod.fst value
  have snd : V choice.2 = j.val := congrArg Prod.snd value
  have beginAddr : V start = V counts + blockId z*stride := by
    change V counts+V p.block*stride = _
    rw [hb]
  rw [generateWidth,rowAt_hit W data mem vs _ _ _ hp]
  change (if decide (V p.slot=0) then V (externalWidth C remaining p.block e.1.1.2)
    else V (rowAt h (fun sl => rowAt (k+1) (fun f =>
      outputWidth (fun b => pool f b e.1.1.2 sl) start choice.1 (bits f)) choice.2) (.cut p.slot (.lit 1)))) = _
  simp only [hs,decide_eq_true_eq,numberedWidth]
  split_ifs with zero live
  · exact externalWidth_read G data mem vs C _ _ z _ stored hr hb
  · let cell : Fin h := ⟨e.1.2.val-1,live⟩
    have hit : V (.cut p.slot (.lit 1)) = cell.val := congrArg (·-1) hs
    rw [rowAt_hit W data mem vs _ _ cell hit,rowAt_hit W data mem vs _ _ j snd,outputWidth_value,fst,beginAddr]
  · apply rowAt_miss
    change h ≤ V p.slot-1
    rw [hs]
    omega


end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
