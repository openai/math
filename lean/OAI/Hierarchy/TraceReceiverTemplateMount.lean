import OAI.Hierarchy.TraceReceiverTemplate
import OAI.Hierarchy.GridReceiverHeader
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Mounting the immutable verifier template from the receiver's own bit tape -/

namespace Hierarchy.TraceReceiverTemplate

open ThreeFlat Diagonal RAM Computability.VPVNP.BurstRAM PrivateRAM
open RAM.PhysicalProcedure
open scoped Fin.CommRing

variable {W n : ℕ}

def image (dst : ℕ) (v : Fin n → Word W) (m : Memory W) : Memory W :=
  fillSegment dst n (fun a => if h : a-dst < n then v ⟨a-dst,h⟩ else 0) m

@[simp] theorem image_at (dst : ℕ) (v : Fin n → Word W) (m : Memory W) (i : Fin n) :
    image dst v m (dst+i.val) = v i := by simp [image, fillSegment, i.isLt]

theorem image_outside (dst : ℕ) (v : Fin n → Word W) (m : Memory W) {a : ℕ}
    (outside : a < dst ∨ dst+n ≤ a) : image dst v m a = m a := by
  have : ¬(dst ≤ a ∧ a < dst+n) := by omega
  simp [image,fillSegment,this]

/-- Fifteen instructions and four structural parameters decode an arbitrary
number of MSB-first words contiguously from the input header. -/
theorem mount (v : Fin n → Word W) (src dst : ℕ)
    (apart : dst+n ≤ src ∨ src+W*n ≤ dst) (fitDst : dst+n < 2^W)
    (fitBits : src+W*n < 2^W) :
    (PhysicalInputPhases.packing W src dst n).Spec
      (fun m => ∀ (i : Fin n) (j : Fin W), m (src+W*i.val+j.val) =
        (((v i).val.testBit (W-1-j.val)).toNat : Word W))
      (fun m m' => m' = image dst v m) (n*(5*W+6)+6) := by
  intro P r K M pc reg pub exit installed data c m entry bits
  change Fin 15 ↪ Fin P at pc
  change Fin 8 ↪ Fin r at reg
  change Fin 4 → Fin K at pub
  change (PackWordBlock.block W).Installed M pc reg pub exit at installed
  let word : ℕ → Word W := fun a => if h : a-dst < n then v ⟨a-dst,h⟩ else 0
  obtain ⟨out,run,atExit⟩ := PackWordBoot.generate_disjoint M (PackWordBlock.headPC pc)
    (PackWordBlock.loopPC pc) reg pub exit
    (fun i => by simpa only [PackWordBlock.block,PackWordBlock.headPC,Fin.addCases_left] using installed (i.castAdd 10))
    (fun i => by simpa only [PackWordBlock.block,PackWordBlock.loopPC,Fin.addCases_right] using installed (Fin.natAdd 5 i))
    src dst n word c m entry data apart fitDst fitBits (by
      intro i hi j hj
      simpa [word,hi] using bits ⟨i,hi⟩ ⟨j,hj⟩)
  exact ⟨_,le_rfl,out,_,run,atExit,rfl⟩

/-- A receiver header stores structural word zero immediately after the tick
index word. Indexing at `first+i` accounts for the preceding directory. -/
theorem header_param {w ell : ℕ} (text : ℕ) (fits : text≤w^2) (raw : Fin (w^2) → Bool)
    (index : Word (64*w)) (params : Fin n → Word (64*w)) (sel : Fin ell → Bool)
    (i : Fin n) (j : Fin (64*w)) :
    let addr := finProdFinEquiv (i.succ,j)
    (GridReceiverHeader.header text fits raw index params sel)[text+addr.val]'(by
      rw [GridReceiverHeader.length]; have := addr.isLt; omega) =
      (params i).val.testBit (64*w-1-j.val) := by
  dsimp only
  unfold GridReceiverHeader.header
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simpa using (finProdFinEquiv (i.succ,j)).isLt)]
  rw [List.getElem_ofFn]
  change GridReceiverHeader.wordBits (64*w) (Fin.cons index params) (finProdFinEquiv (i.succ,j)) = _
  rw [GridReceiverHeader.word_at]
  rfl

end Hierarchy.TraceReceiverTemplate

end OAI
