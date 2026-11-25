import OAI.Computability.BorderVNP.CellSparseExteriorBatchRun
import OAI.Computability.BorderVNP.CellPacketSupplementalBatchTyped

/-! # Binding the actual sparse preparation postimage to the typed task initializer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellPacket CellPacketEncode

/-- The original descriptor stream, scratch arena, burst and call row are used by
the same initializer. Its two external operands now refer to the actual encoded buffer. -/
def Owned.typed (o : Owned) (l : Layout) (original : TypedBatch.Task) : TypedBatch.Task :=
  { original with cell := { original.cell with externalBase := o.dest l, external := o.field.bytes } }

/-- Every source of the true typed initializer except the separately produced
RLE external array. Includes the actual opaque original-site data. -/
def TypedSources (t : TypedBatch.Task) (a : ℕ) :=
  (t.cell.descriptorBase ≤ a ∧ a<t.cell.descriptorBase+3*t.cell.chunks.length) ∨
  ∃ c ∈ t.cell.chunks, c.base ≤ a ∧ a<c.endSource

/-- Numerically distinct result rows and compact intervals preserve every already
published field and every future initializer read. -/
structure Protected (l : Layout) (owned : ℕ → Owned) (original : ℕ → TypedBatch.Task) : Prop where
  scalar : ∀ i < l.count, ∀ j < l.count, ∀ k ∈ [0,1,4,5,6], (owned j).Outside l j (l.tasks+7*i+k)
  bytes : ∀ i < l.count, ∀ k < (owned i).field.bytes.length, ∀ j < l.count, j ≠ i → (owned j).Outside l j ((owned i).dest l+k)
  self : ∀ i < l.count, ∀ k < (owned i).field.bytes.length, let a := (owned i).dest l+k
    a ≠ l.tasks+7*i+2 ∧ a ≠ l.tasks+7*i+3 ∧ a ≠ l.counts+(owned i).global
  counter : ∀ i < l.count, l.counts+(owned i).global ≠ l.tasks+7*i+2 ∧ l.counts+(owned i).global ≠ l.tasks+7*i+3
  row : ∀ i < l.count, ∀ j < l.count, j ≠ i → ∀ k ∈ [2,3], (owned j).Outside l j (l.tasks+7*i+k)
  original : ∀ i < l.count, ∀ a, TypedSources (original i) a → ∀ j < l.count, (owned j).Outside l j a

variable {w : ℕ}

/-- Every initializer reads exactly its patched row and the physically staged
compact external data. The original geometrical descriptors and their opaque
body sources stay valid through the complete owning-team scan. -/
theorem stored_after (l : Layout) (owned : ℕ → Owned) (original : ℕ → TypedBatch.Task)
    (m mt : Memory w) (post : readings mt=written l owned (readings m) l.count) (safe : Protected l owned original)
    (i : ℕ) (hi : i<l.count) (row : (original i).Stored m l.tasks i)
    (desc : WordsAt (readings m) (original i).cell.descriptorBase (descriptors (original i).cell.chunks))
    (chunks : ∀ c ∈ (original i).cell.chunks, c.Stored (readings m)) :
    ((owned i).typed l (original i)).Stored mt l.tasks i ∧ ((owned i).typed l (original i)).cell.Stored mt := by
  let o := owned i
  let t := original i
  have keep (a : ℕ) (h : ∀ j < l.count, (owned j).Outside l j a) : readings mt a = readings m a := by
    rw [post]; exact written_preserve l owned (readings m) (i:=0) (Nat.zero_le _) _ (fun j _ hj => h j hj)
  have scalar (k : ℕ) (hk : k ∈ [0,1,4,5,6]) : readings mt (l.tasks+7*i+k) = readings m (l.tasks+7*i+k) :=
    keep _ (fun j hj => safe.scalar i hi j hj k hk)
  have later (a : ℕ) (h : ∀ j, i<j → j<l.count → (owned j).Outside l j a) :
      readings mt a = o.image l i (written l owned (readings m) i) a := by
    rw [post]; exact written_preserve l owned (readings m) (i:=i+1) hi a (fun j hj hlt => h j hj hlt)
  have newRow (k : ℕ) (hk : k ∈ [2,3]) := later (l.tasks+7*i+k) (fun j hj hlt => safe.row i hi j hlt hj.ne' k hk)
  have off := safe.counter i hi
  have ptr : readings mt (l.tasks+7*i+2) = o.dest l := by
    rw [newRow 2 (by decide),Owned.image,Function.update_of_ne off.1.symm,Function.update_of_ne (by omega),Function.update_self]
  have num : readings mt (l.tasks+7*i+3) = o.field.bytes.length := by
    rw [newRow 3 (by decide),Owned.image,Function.update_of_ne off.2.symm,Function.update_self]
  have source (a : ℕ) (h : TypedSources t a) := keep a (safe.original i hi a h)
  obtain ⟨a,b,_,_,d,e,f⟩ := row
  refine ⟨⟨(scalar 0 (by decide)).trans a,(scalar 1 (by decide)).trans b,ptr,num,
    (scalar 4 (by decide)).trans d,(scalar 5 (by decide)).trans e,(scalar 6 (by decide)).trans f⟩,
    ⟨?_,?_,?_⟩⟩
  · intro j
    change readings mt (t.cell.descriptorBase+j.val)=_
    have lt := j.isLt.trans_eq (descriptors_length t.cell.chunks)
    rw [source _ (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left lt _⟩)]
    exact desc j
  · intro c hc
    exact (chunks c hc).congr (fun a h₁ h₂ => source a (.inr ⟨c,hc,h₁,h₂⟩))
  · intro k hk
    have last := later (o.dest l+k) (fun j hj hlt => safe.bytes i hi k hk j hlt hj.ne')
    obtain ⟨d₁,d₂,d₃⟩ := safe.self i hi k hk
    change readings mt (o.dest l+k) = o.field.bytes[k].toNat
    rw [last,Owned.image,Function.update_of_ne d₃,Function.update_of_ne d₂,Function.update_of_ne d₁]
    exact putDigits_read _ _ _ ⟨k,hk⟩

/-- Replacing the two exterior operands supplies the same original private
directory and exactly the encoded suffix specified by the physical driver. -/
theorem Owned.typed_payload (o : Owned) (l : Layout) (t : TypedBatch.Task) (D : CellSparse.Directory) (p : ℕ)
    (packet : t.cell.packet=CellSparse.Packet.bits D p) :
    (o.typed l t).cell.payload = CellSparse.Packet.input D p o.field.bytes := by
  change envelope t.cell.packet o.field.bytes = _
  rw [packet]; rfl

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
