import OAI.ThreeFlat.RAM.TickSlotStep

namespace OAI
/-! # Reading the scheduler's physical per-vertex owner table -/

namespace ThreeFlat.RAM.TickSlotLookup

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing

variable {w p r k : ℕ}

def selected (own : Owner w) (g s : Word w) (i rem : ℕ) : List ℕ :=
  (List.range' i rem).filter (matchesOwner own g s)

private theorem loop (M : Machine w p r k) (pc : Fin 11 → Fin p) (R : Fin 9 ↪ Fin r) (exit : Fin p)
    (rom : ∀ j, M.code (pc j) = code pc R exit j) (own : Owner w) (g s : Word w)
    (rem i n src dst count : ℕ) (c : Config w p r) (m : Memory w) (start : c.pc = pc 0)
    (h : Ready R c i n src dst count g s) (en : i+rem=n) (nw : n<2^w)
    (sw : src+2*rem < 2^w) (dw : dst+rem < 2^w)
    (sep : dst ≤ src ∨ src+2*rem ≤ dst)
    (rows : ∀ j < rem, m (src+2*j) = (own (i+j)).1 ∧ m (src+2*j+1) = (own (i+j)).2) :
    let vs := selected own g s i rem
    ∃ t ≤ 1+11*rem, ∃ d, advance M.program t c m = some (d,store m dst vs) ∧
      d.pc = exit ∧ Ready R d n n (src+2*rem) (dst+vs.length) (count+vs.length) g s ∧
      d.persistent = c.persistent ∧ d.privateMem = c.privateMem := by
  induction rem generalizing i src dst count c m with
  | zero =>
    have same : c.reg (R 0) = c.reg (R 1) := by
      have eq : i=n := by simpa only [Nat.add_zero] using en
      rw [h.1,h.2.1,eq]
    refine ⟨1,by omega,{c with pc := exit},?_,rfl,?_,rfl,rfl⟩
    · simp [selected,store,advance,Machine.program,start,rom,code,Instr.run,same]
    · simpa [selected,Ready,← en] using h
  | succ rem ih =>
    let hit := matchesOwner own g s i
    let nextMem := if hit then put m dst i else m
    have room : hit.toNat ≤ 1 := by cases hit <;> decide
    obtain ⟨t,ht,b,brun,bpc,bok,bper,bpriv⟩ := advance_row M pc R exit rom own g s i n src dst count c m
      start h (by omega) nw (by omega) (by omega)
      (by simpa using (rows 0 (by omega)).1) (by simpa using (rows 0 (by omega)).2)
    have retained (q : ℕ) (lo : src+2 ≤ q) (hi : q < src+2*(rem+1)) : nextMem q = m q := by
      have ne : q ≠ dst := by omega
      cases eq : hit <;> simp [nextMem,eq,put,ne]
    have nextRows (j : ℕ) (hj : j < rem) :
        nextMem (src+2+2*j) = (own (i+1+j)).1 ∧ nextMem (src+2+2*j+1) = (own (i+1+j)).2 := by
      obtain ⟨hg,hs⟩ := rows (j+1) (by omega)
      rw [retained _ (by omega) (by omega),retained _ (by omega) (by omega)]
      simpa only [Nat.mul_succ,add_assoc,add_comm,add_left_comm] using And.intro hg hs
    obtain ⟨u,hu,d,drun,dpc,dok,dper,dpriv⟩ := ih (i+1) (src+2) (dst+hit.toNat) (count+hit.toNat)
      b nextMem bpc bok (by omega) (by omega) (by omega) (by omega) nextRows
    have run := advance_trans brun drun
    refine ⟨t+u,by omega,d,?_,dpc,?_,dper.trans bper,dpriv.trans bpriv⟩
    · cases eq : matchesOwner own g s i <;>
        simpa [selected,List.range'_succ,hit,
          eq,nextMem,store] using run
    · cases eq : matchesOwner own g s i <;>
        simpa [selected,List.range'_succ,hit,eq,
          Nat.mul_succ,add_assoc,add_left_comm,add_comm] using dok

/-- Three instructions initialize the current vertex, selected count, and unit.
The other arguments (table pointers, end, requested group, and requested slot)
are incoming word registers of the caller. -/
def header (pc : Fin 3 → Fin p) (R : Fin 9 ↪ Fin r) (entry : Fin p) : Fin 3 → Instr w p r k
  | 0 => .constant (R 0) 0 (pc 1)
  | 1 => .constant (R 4) 0 (pc 2)
  | _ => .constant (R 7) 1 entry

/-- The resulting dense list contains precisely the vertices of the requested
group and slot, in increasing index order. The selected-count register and
output pointer identify its exact extent. The scan also supports in-place
compaction into the owner table itself. -/
theorem advance_selected (M : Machine w p r k) (setup : Fin 3 → Fin p) (pc : Fin 11 → Fin p)
    (R : Fin 9 ↪ Fin r) (exit : Fin p)
    (head : ∀ j, M.code (setup j) = header setup R (pc 0) j)
    (rom : ∀ j, M.code (pc j) = code pc R exit j)
    (own : Owner w) (g s : Word w) (n src dst : ℕ) (c : Config w p r) (m : Memory w)
    (start : c.pc = setup 0) (endReg : c.reg (R 1) = (n : Word w))
    (srcReg : c.reg (R 2) = (src : Word w)) (dstReg : c.reg (R 3) = (dst : Word w))
    (gReg : c.reg (R 5) = g) (sReg : c.reg (R 6) = s)
    (nw : n<2^w) (sw : src+2*n < 2^w) (dw : dst+n < 2^w)
    (sep : dst ≤ src ∨ src+2*n ≤ dst)
    (rows : ∀ j < n, m (src+2*j) = (own j).1 ∧ m (src+2*j+1) = (own j).2) :
    let vs := (List.range n).filter (matchesOwner own g s)
    ∃ t ≤ 4+11*n, ∃ d, advance M.program t c m = some (d,store m dst vs) ∧ d.pc = exit ∧
      (d.reg (R 4)).val = vs.length ∧ (d.reg (R 3)).val = dst+vs.length ∧
      d.persistent = c.persistent ∧ d.privateMem = c.privateMem := by
  let b := ((c.put (setup 1) (R 0) 0).put (setup 2) (R 4) 0).put (pc 0) (R 7) 1
  have init : advance M.program 3 c m = some (b,m) := by
    simp [advance,Machine.program,start,head,header,Instr.run,b,Config.put]
  have ok : Ready R b 0 n src dst 0 g s := by
    simp (config := {decide := true}) [b,Ready,Config.put,Function.update,R.injective.eq_iff,
      endReg,srcReg,dstReg,gReg,sReg]
  obtain ⟨t,ht,d,run,dpc,dok,dp,dm⟩ := loop M pc R exit rom own g s n 0 n src dst 0 b m rfl ok
    (by omega) nw sw dw sep (by simpa using rows)
  have len : (selected own g s 0 n).length ≤ n := by
    simpa only [selected,List.length_range'] using (List.length_filter_le (matchesOwner own g s) (List.range' 0 n))
  have hn : selected own g s 0 n = (List.range n).filter (matchesOwner own g s) := by rw [selected,List.range_eq_range']
  obtain ⟨_,_,_,outReg,numReg,_⟩ := dok
  refine ⟨3+t,by omega,d,by simpa only [hn] using advance_trans init run,dpc,?_,?_,dp,dm⟩
  · rw [numReg,Nat.zero_add,Fin.val_cast_of_lt (len.trans_lt nw),hn]
  · rw [outReg,Fin.val_cast_of_lt (by omega),hn]

end ThreeFlat.RAM.TickSlotLookup

end OAI
