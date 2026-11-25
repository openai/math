import OAI.Computability.BorderVNP.CellPacketSupplementalMemory
import OAI.Computability.BorderVNP.CellPacketInitializerCost

/-! # Sparse resource bounds with true sidecar-dependent use-check records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement

open VPVNP.BurstRAM CellSparse CellSparse.Packet CellSparse.Packet.Source RationalHitting.StackLanguage

variable {w : ℕ} {Site : Type}

/-- Each physical integer word contributes at most a word-width factor. Each
opaque body is scanned just once together with its one length header. -/
def chunkUnits (w : ℕ) : Chunk → ℕ
  | .words _ xs => (w+1)*(xs.length+1)
  | .box _ H bs => H+bs.length+1

private theorem chunk_work (w : ℕ) (c : Chunk) : c.work w = 60*chunkUnits w c := by
  cases c <;> simp [Chunk.work,chunkUnits]
  ring

private theorem source_length (m : Memory w) (c : Chunk) (src : c.Stored (readings m)) :
    c.bits.length ≤ 2*chunkUnits w c := by
  cases c with
  | box a H bs => simp only [Chunk.bits,chunkUnits]; omega
  | words a xs =>
    have bound (x : ℕ) (hx : x ∈ xs) : x < 2^w := by
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
      exact (src ⟨i,hi⟩).symm.trans_lt (m (a+i)).isLt
    have h := CellPacketEncode.packet_length_le xs bound
    change (CellPacketEncode.packet xs).length ≤ 2*((w+1)*(xs.length+1))
    nlinarith

private theorem totals (m : Memory w) (cs : List Chunk) (src : ∀ c ∈ cs, c.Stored (readings m)) :
    (cs.flatMap Chunk.bits).length ≤ 2*(cs.map (chunkUnits w)).sum ∧
      cs.length ≤ (cs.map (chunkUnits w)).sum ∧
      (cs.map (Chunk.work w)).sum = 60*(cs.map (chunkUnits w)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨length,count,work⟩ := ih fun b h => src b (List.mem_cons_of_mem _ h)
    have head := source_length m c (src c List.mem_cons_self)
    have pos : 0 < chunkUnits w c := by cases c <;> simp [chunkUnits]
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,List.length_cons,chunk_work w c,work]
    omega

/-- Resource units of the revised packet, including four tail descriptors and the
supplemental words actually produced from the original descriptions. -/
def units (p : Placed Site) (extra : List Record) (w description : ℕ) :=
  p.units w description + (w+1)*(3+(extra.flatMap record).length)

private theorem parts_units (p : Placed Site) (ps : List (CellSparse.Packet.Source.Part Site))
    (base description : ℕ) (room : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description) :
    ((chunks p.slot p.headerWidth p.factors base ps).map (chunkUnits w)).sum ≤
      (w+1)*((ps.flatMap Part.publicBuffer).length+ps.length)+(description+1)*(privateKeys ps).length := by
  induction ps generalizing base with
  | nil => simp [chunks,privateKeys]
  | cons a ps ih =>
    cases a with
    | publicWords xs =>
      have h := ih (base+xs.length)
      simp only [chunks,List.map_cons,List.sum_cons,chunkUnits,List.flatMap_cons,Part.publicBuffer,
        List.length_append,List.length_cons,privateKeys,List.filterMap_cons_none] at h ⊢
      linarith
    | original j =>
      have h := ih base
      have key : (privateKeys (Part.original j::ps)).length = (privateKeys ps).length+1 := rfl
      rw [key]
      simp only [chunks,List.map_cons,List.sum_cons,chunkUnits,List.flatMap_cons,Part.publicBuffer,
        List.nil_append,List.length_cons] at h ⊢
      nlinarith only [h,room j,Nat.zero_le w]

private theorem revised_units (p : Placed Site) (l : Layout) (base : ℕ) (extra : List Record)
    (description : ℕ) (room : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description) :
    (((task l p base extra).chunks.map (chunkUnits w)).sum+1+(task l p base extra).external.length) ≤
      units p extra w description := by
  have h := parts_units (w := w) p (prefixParts p) p.publicBase description room
  have shape : p.parts = prefixParts p ++ [.publicWords (fieldList record p.rows++fieldList vector p.reports)] := by
    simp [Placed.parts,plan,prefixParts]
  simp only [task,List.map_append,List.sum_append,prefixChunks,tailChunks,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,chunkUnits,List.length_cons,List.length_nil,units,Placed.units,shape,
    List.flatMap_append,List.flatMap_cons,List.flatMap_nil,Part.publicBuffer,List.append_nil,List.length_append,
    privateKeys,List.filterMap_append,List.filterMap_cons_none,List.filterMap_nil,fieldList] at h ⊢
  change _ + 1 + p.external.length ≤ _
  nlinarith only [h,Nat.zero_le w]

/-- The original bounds on true native initializer ticks, scratch words and
burst words still hold with the additional three descriptors and the dynamically
emitted use-check records. A separate 42-tick fixed arithmetic prepass suffices. -/
theorem limits (p : Placed Site) (l : Layout) (base : ℕ) (extra : List Record)
    (m : Memory w) (description : ℕ) (hw : 0 < w)
    (src : (task l p base extra).Stored m)
    (room : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description) :
    let t := task l p base extra
    let U := units p extra w description
    t.cost w ≤ 300*U ∧ t.payload.length ≤ 4*U ∧ (t.burst w).length ≤ (8*U)/w+1 := by
  intro t U
  have compact := revised_units (w := w) p l base extra description room
  change (t.chunks.map (chunkUnits w)).sum+1+t.external.length ≤ U at compact
  obtain ⟨packet,count,work⟩ := totals m t.chunks src.chunks
  change t.packet.length ≤ _ at packet
  have finish := finishCost_le t.packet t.external
  have length : t.payload.length = 2*t.packet.length+1+t.external.length := by
    simp [Task.payload,envelope,codeWord_length]
  have scratch : t.payload.length ≤ 4*U := by omega
  refine ⟨?_,scratch,?_⟩
  · rw [Task.cost,chunksCost_eq,work]
    omega
  · rw [Task.burst,CompactFrame.length_pack,←CompactFrame.wordCount,CompactFrame.wordCount_terminator hw]
    exact Nat.succ_le_succ (Nat.div_le_div_right (by omega))

end RoutingISA.CellPacket.Supplement

end BorderVNP
end Computability
end OAI
