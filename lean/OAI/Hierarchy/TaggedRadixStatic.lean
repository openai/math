import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Rectangular row maps and their fixed Boolean padding -/

namespace Hierarchy.Tagged.RadixStage
noncomputable section
variable {I O : Type}

abbrev StaticMap (I O : Type) := O → I ⊕ Bool

def staticRead (wire : StaticMap I O) (x : I → Bool) (p : O) := Sum.elim x id (wire p)

abbrev RowBits (n w : ℕ) := Fin n × Fin w

/-- Split the real input into fixed logical blocks. Extra physical lanes in
each block and the unfinished suffix of the last block use the dummy word. -/
def blockScatter (n blocks logical physical w : ℕ) (dummy : Fin w → Bool) :
    StaticMap (RowBits n w) (Fin blocks × RowBits physical w) := fun ⟨b,lane,bit⟩ =>
  if lane.val < logical then
    if h : b.val*logical+lane.val < n then .inl (⟨b.val*logical+lane.val,h⟩,bit)
    else .inr (dummy bit)
  else .inr (dummy bit)

/-- Clip each block to its fixed output capacity, dropping physical slots
reserved solely for padding to a power-of-two address length. -/
def collectBlocks {blocks logical physical w : ℕ} (fits : logical ≤ physical) :
    StaticMap (Fin blocks × RowBits physical w) (RowBits (blocks*logical) w) := fun ⟨row,bit⟩ =>
  let bs := finProdFinEquiv.symm row
  .inl (bs.1,Fin.castLE fits bs.2,bit)

/-- Reinterpret a rectangle of words as wide consecutive packs. -/
def packWire {packs p w : ℕ} : StaticMap (RowBits (packs*p) w) (RowBits packs (p*w)) := fun ⟨r,b⟩ =>
  let lane := finProdFinEquiv.symm b
  .inl (finProdFinEquiv (r,lane.1),lane.2)

def unpackWire {packs p w : ℕ} : StaticMap (RowBits packs (p*w)) (RowBits (packs*p) w) := fun ⟨r,b⟩ =>
  let row := finProdFinEquiv.symm r
  .inl (row.1,finProdFinEquiv (row.2,b))

end
end Hierarchy.Tagged.RadixStage

end OAI
