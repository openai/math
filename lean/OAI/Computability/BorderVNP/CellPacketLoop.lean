import OAI.Computability.BorderVNP.CellPacketDispatch

/-! # The native scan of a cell's sparse source descriptors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM CellPacketEncode

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Scan exactly the half-open interval of descriptors for the selected cell. -/
def chunksLoop : Code := .whileLt 2 3 oneChunk

/-- Runtime for the descriptor loop, with one terminal guard and eight non-encoding
ticks per range for reading the descriptor and testing the guard. -/
def chunksCost (w : ℕ) : List Chunk → ℕ
  | [] => 1
  | c::cs => 1+(7+c.work w)+chunksCost w cs

/-- Exact memory effect of the chunk scan. -/
def chunkResult (s : Bank w) (m : Memory w) (cs : List Chunk) (a dst : ℕ) (z : NatState) : Prop :=
  Persistent (readings s) z.reg ∧ z.reg 2 = a+3*cs.length ∧
  z.reg 20 = dst+(tags true (cs.flatMap Chunk.bits)).length ∧
  z.mem = putDigits (readings m) dst (tags true (cs.flatMap Chunk.bits))

/-- Scratch writes preserve a physical descriptor array that ends before the scratch. -/
theorem WordsAt.putDigits {mem : ℕ → ℕ} {a dst : ℕ} {xs : List ℕ} (h : WordsAt mem a xs)
    (bound : a+xs.length ≤ dst) (bs : List Bool) : WordsAt (putDigits mem dst bs) a xs := by
  intro i
  rw [putDigits_outside _ _ _ _ (.inl (by have := i.isLt; omega))]
  exact h i

/-- The physical word machine reads only the descriptors in this cell. Each chunk's
source is taken from memory, with the true length of each private box parsed from its
opaque header. The resulting scratch interval is the concatenated pair-tagged stream. -/
theorem chunks_run (cs : List Chunk) (s : Bank w) (m : Memory w) (a dst : ℕ)
    (hc : Constants (readings s)) (cursor : readings s 2 = a)
    (limit : readings s 3 = a+3*cs.length) (write : readings s 20 = dst)
    (table : WordsAt (readings m) a (descriptors cs))
    (source : ∀ c ∈ cs, c.Stored (readings m))
    (apart : ∀ c ∈ cs, c.endSource ≤ dst) (tableEnd : a+3*cs.length ≤ dst)
    (fit : dst+(tags true (cs.flatMap Chunk.bits)).length < 2^w) :
    BoundedRun pub macros chunksLoop s m (chunksCost w cs) (chunkResult s m cs a dst) := by
  induction cs generalizing s m a dst with
  | nil =>
    have guard : ¬ s 2 < s 3 := show ¬ readings s 2 < readings s 3 by simp [cursor,limit]
    apply loop_done guard
    simpa only [chunkResult,List.length_nil,Nat.mul_zero,Nat.add_zero,List.flatMap_nil,tags_nil,
      putDigits,NatState.ofWords] using
      (show Persistent (readings s) (readings s) ∧ readings s 2 = a ∧ readings s 20 = dst ∧ readings m = readings m
        from ⟨fun _ _ => rfl,cursor,write,rfl⟩)
  | cons c cs ih =>
    let part := tags true c.bits
    let rest := tags true (cs.flatMap Chunk.bits)
    have split : tags true ((c::cs).flatMap Chunk.bits) = part++rest := by
      simp [part,rest]
    have len : c.descriptor.length = 3 := by cases c <;> rfl
    change WordsAt (readings m) a (c.descriptor++descriptors cs) at table
    rw [split,List.length_append] at fit
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at limit tableEnd
    have guard : s 2 < s 3 := show readings s 2 < readings s 3 by omega
    have first := oneChunk_run (pub := pub) (macros := macros) c s m a cursor hc table.left
      (source c (by simp)) (by omega) (write ▸ apart c (by simp)) (by change readings s 20+part.length<2^w; omega)
    apply loop_step guard first
    rintro t mt ⟨per,cur,advance,mem⟩
    change readings t 2 = a+3 at cur
    change readings t 20 = readings s 20 + part.length at advance
    change readings mt = putDigits (readings m) (readings s 20) part at mem
    rw [write] at advance mem
    have end' : readings t 3 = a+3+3*cs.length := by
      change (NatState.ofWords t mt).reg 3 = _
      rw [per 3 (by decide)]; omega
    have table' : WordsAt (readings mt) (a+3) (descriptors cs) := by
      rw [mem]
      apply WordsAt.putDigits
      · simpa only [len] using table.right
      · rw [descriptors_length]; omega
    have source' : ∀ b ∈ cs, b.Stored (readings mt) := by
      intro b hb
      rw [mem]
      exact (source b (List.mem_cons_of_mem _ hb)).putDigits (apart b (List.mem_cons_of_mem _ hb)) part
    have run := ih t mt (a+3) (dst+part.length) (per.constants hc) cur end' advance table' source'
      (fun b hb => (apart b (List.mem_cons_of_mem _ hb)).trans (Nat.le_add_right _ _)) (by omega)
      (by change dst+part.length+rest.length < 2^w; omega)
    apply run.mono le_rfl
    rintro z ⟨fixed,pos,dest,out⟩
    refine ⟨per.trans fixed,?_,?_,?_⟩
    · simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega
    · rw [split,List.length_append]
      change z.reg 20 = dst+part.length+rest.length at dest
      omega
    · rw [split,putDigits_append,←mem]
      exact out

/-- The loop charge is additive in the compact descriptors, even when their encoded
box records specify arbitrary copy multiplicities. -/
theorem chunksCost_eq (w : ℕ) (cs : List Chunk) :
    chunksCost w cs = 1+8*cs.length+(cs.map (Chunk.work w)).sum := by
  induction cs with
  | nil => simp [chunksCost]
  | cons c cs ih =>
    simp only [chunksCost,ih,List.length_cons,Nat.mul_add,Nat.mul_one,List.map_cons,List.sum_cons]
    omega

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
