import OAI.Computability.BorderVNP.RoutingISABlockAppend
import OAI.Computability.BorderVNP.CubeISASelectorRead
import OAI.Computability.BorderVNP.CubeISARowAccumPhysical

/-! # Native packet callback for the owned symbol-row scan

The stable register 8 points at eight metadata words. They specify the selector
bit width and number of terms, edge radix, row base, dimension, digit-scratch
base, slot count and edge width. The packet base in register 24 comes from the
owned candidate iterator. Only the row and the digit scratch can change in memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.PacketTally

open RoutingISA VPVNP.BurstRAM Cube.Physical Cube.Tally
open scoped Classical

/-- The declared metadata agrees with the chosen physical cube instance. -/
structure Header (mem : ℕ → ℕ) (addr n K h row scratch s : ℕ) : Prop where
  /-- Bits per selector prefix. -/
  bits : mem (addr+0) = selectorWidth n K h
  /-- Number of valid mixed-radix selector ordinals. -/
  terms : mem (addr+1) = Fintype.card (Selector n K h)
  /-- Radix of the ordered edge tuple. -/
  radix : mem (addr+2) = Fintype.card (Edge (n+1))
  /-- Beginning of the current physical pair row. -/
  rowBase : mem (addr+3) = row
  /-- Number of candidate cut directions. -/
  dimension : mem (addr+4) = n+1
  /-- Temporary array for the decoded edge ordinals. -/
  digits : mem (addr+5) = scratch
  /-- Number of edge slots in the selector. -/
  count : mem (addr+6) = h
  /-- Width assigned to each selected edge. -/
  edgeWidth : mem (addr+7) = s

/-- Read an offset of the metadata relative to register 8. -/
def loadField (dst : Reg) (offset : Word 8) : RoutingISA.Code := .block [
  .constant 62 offset, .binary .add 62 8 62, .load dst 62]

/-- Install the selector reader and the accumulator's actual input registers. -/
def setup : RoutingISA.Code := .block [loadField 41 0,loadField 42 1,loadField 44 2,loadField 45 3,
  loadField 46 4,loadField 47 5,loadField 48 6,loadField 49 7]

/-- Read and validate a packet's genuine selector and add its edge contributions. -/
def callback : RoutingISA.Code := .seq setup (.seq SelectorRead.reader RowAccum.packetFromSelector)

/-- Slot and loop allowance for one accepted packet callback. -/
def cost (n K h : ℕ) := setup.slots + (SelectorRead.init.slots+
  selectorWidth n K h*(SelectorRead.step.slots+1)+1+(requireLt 43 42).slots + (15*h+7))

private theorem fieldSafe {w : ℕ} (dst : Reg) (f : Word 8) (p : Arg → ℕ) (m : ℕ → ℕ)
    (reg : Reg → ℕ) (addr : reg 8+f.val < 2^w) :
    (loadField dst f).safeReadOnly w p m reg := by
  simp (config := {decide := true}) [loadField,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits,addr]
  omega

private theorem fieldValue (dst : Reg) (f : Word 8) (p : Arg → ℕ) (m : ℕ → ℕ) (reg : Reg → ℕ) :
    (loadField dst f).evalNat p m reg =
      Function.update (Function.update reg 62 (reg 8+f.val)) dst (m (reg 8+f.val)) := by
  simp (config := {decide := true}) [loadField,Code.block,Code.evalNat,addressOp]

private structure Inputs (r : Reg → ℕ) (n K h row scratch s : ℕ) : Prop where
  width : r 41 = selectorWidth n K h
  terms : r 42 = Fintype.card (Selector n K h)
  radix : r 44 = Fintype.card (Edge (n+1))
  rowBase : r 45 = row
  dimension : r 46 = n+1
  digits : r 47 = scratch
  count : r 48 = h
  edgeWidth : r 49 = s

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem setup_run (r : Bank w) (m : Memory w) (n K h row scratch s : ℕ)
    (head : Header (readings m) (readings r 8) n K h row scratch s)
    (addr : readings r 8+7 < 2^w) :
    BoundedRun pub mac setup r m setup.slots (fun z => z.mem = readings m ∧
      (∀ j : Reg, j.val < 41 → z.reg j = readings r j) ∧ Inputs z.reg n K h row scratch s) := by
  let reg := readings r
  let p := readings pub
  let mem := readings m
  have sa (dst : Reg) (f : Word 8) (hf : f.val ≤ 7) (z : Reg → ℕ) (keep : z 8 = reg 8) :
      (loadField dst f).safeReadOnly w p mem z := fieldSafe _ _ _ _ _ (by rw [keep]; change readings r 8+_ < _; omega)
  have safe : setup.safeReadOnly w p mem reg := by
    simp only [setup,Code.block,Code.safeReadOnly]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals apply sa _ _ (by decide); simp (config := {decide := true}) [fieldValue]
  obtain ⟨es,t,run,cap,eq⟩ := setup.runReadOnly pub mac m r safe
  refine ⟨es,t,m,run,cap,rfl,fun j hj => (congrFun eq j).trans (setup.evalNat_protected _ _ _ (by decide) j hj),?_⟩
  change Inputs (readings t) _ _ _ _ _ _
  rw [eq]
  obtain ⟨a,b,c,d,e,f,g,q⟩ := head
  simp only [Nat.add_zero] at a
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp (config := {decide := true}) [setup,Code.block,Code.evalNat,fieldValue,a,b,c,d,e,f,g,q]

/-- The unique decoded selector, with an empty result for malformed inputs. -/
noncomputable def selection (n K h : ℕ) (mem : ℕ → ℕ) (base : ℕ) : Option (Selector n K h) :=
  if good : SelectorRead.Valid mem base (selectorWidth n K h) (Fintype.card (Selector n K h))
    then some ((selectorOrder n K h).symm ⟨_,good.2⟩) else none

/-- A stored legal selector is precisely the one decoded by the callback. -/
theorem selection_of_stored {n K h : ℕ} {mem : ℕ → ℕ} {base : ℕ} {u : Selector n K h}
    (stored : SelectorRead.Stored mem base u) : selection n K h mem base = some u := by
  have valid : SelectorRead.Valid mem base (selectorWidth n K h) (Fintype.card (Selector n K h)) := by
    refine ⟨fun j hj => ?_,stored.rank ▸ (selectorOrder n K h u).isLt⟩
    rw [stored ⟨j,hj⟩]
    exact Nat.lt_succ_of_le (Bool.toNat_le _)
  simp only [selection,dite_eq_left valid,Option.some.injEq]
  apply (selectorOrder n K h).injective
  exact (Equiv.apply_symm_apply ..).trans (Fin.ext stored.rank)

/-- The actual contribution inferred from the packet bits. Its value on a rejected
prefix is zero, so a prefix sum can be defined on every input bank. -/
noncomputable def contribution {n d blocks : ℕ} (K h b s : ℕ) (mem : ℕ → ℕ) (base : ℕ)
    (p : Packet n d blocks) (j : Fin (n+1)) : ℕ :=
  match selection n K h mem base with
  | none => 0
  | some u => crossCount b s (fun _ => u) (.inl p) j

/-- State produced at the end of the concrete native packet callback. -/
def Added {n d blocks : ℕ} (K h b s : ℕ) (mem : ℕ → ℕ) (packet row scratch : ℕ)
    (p : Packet n d blocks) (z : NatState) : Prop :=
  (∀ j : Fin (n+1), z.mem (row+j.val) = mem (row+j.val) + contribution K h b s mem packet p j) ∧
  ∀ a, (a < row ∨ row+(n+1) ≤ a) → (a < scratch ∨ scratch+h ≤ a) → z.mem a = mem a

/-- Native execution accepts exactly the well-formed selector, adds its physical cut
widths, and preserves every word outside the two bounded work arrays. -/
theorem callback_test {n d blocks K h : ℕ} (r : Bank w) (m : Memory w) (p : Packet n d blocks)
    (b s row scratch packet : ℕ) (rp : readings r 24 = packet)
    (head : Header (readings m) (readings r 8) n K h row scratch s)
    (headerRoom : readings r 8+7 < 2^w) (packetRoom : packet+selectorWidth n K h ≤ 2^w)
    (rowRoom : row+(n+1) ≤ 2^w) (digitRoom : scratch+h ≤ 2^w)
    (separate : scratch+h ≤ row ∨ row+(n+1) ≤ scratch)
    (sumRoom : ∀ j < n+1, readings m (row+j)+h*s < 2^w) :
    TestRun pub mac callback r m (cost n K h)
      (SelectorRead.Valid (readings m) packet (selectorWidth n K h) (Fintype.card (Selector n K h)))
      (fun z => Added K h b s (readings m) packet row scratch p z ∧
        ∀ j : Reg, j.val < 41 → z.reg j = readings r j) := by
  let mem := readings m
  let ok := SelectorRead.Valid mem packet (selectorWidth n K h) (Fintype.card (Selector n K h))
  let P (z : NatState) := Added K h b s mem packet row scratch p z ∧
    ∀ j : Reg, j.val < 41 → z.reg j = readings r j
  have first := setup_run (pub := pub) (mac := mac) r m n K h row scratch s head headerRoom
  have second (t : Bank w) (mt : Memory w) (hz : readings mt = mem)
      (low : ∀ j : Reg, j.val < 41 → readings t j = readings r j)
      (input : Inputs (readings t) n K h row scratch s) := by
    have cap : selectorWidth n K h ≤ w := Nat.clog_le_of_le_pow (input.terms ▸ (t 42).isLt.le)
    exact SelectorRead.reader_run (pub := pub) (mac := mac) t mt packet _ _ ((low 24 (by decide)).trans rp)
      input.width input.terms (by omega) cap packetRoom
  have complete (good : ok) : BoundedRun pub mac callback r m (cost n K h) P := by
    obtain ⟨u,stored,_⟩ := (SelectorRead.valid_iff_existsUnique mem packet).mp good
    apply first.seq
    rintro t mt ⟨hm,low,input⟩
    have hm' : readings mt = mem := hm
    have read := (second t mt hm' low input).complete (hm' ▸ good)
    apply read.seq
    rintro v mv ⟨hmv,rank,keep⟩
    have keepReg (j : Reg) (h : ¬SelectorRead.Scratch j) : readings v j = readings t j := keep j h
    have back : readings mv = mem := hmv.trans hm'
    have rk : readings v 43 = (selectorOrder n K h u).val :=
      rank.trans (hm' ▸ stored.rank)
    have run := RowAccum.packetFromSelector_run pub mac v mv row scratch b s (fun _ => u) p
      rk ((keepReg 44 (by simp [SelectorRead.Scratch])).trans input.radix) ((keepReg 45 (by simp [SelectorRead.Scratch])).trans input.rowBase)
      ((keepReg 46 (by simp [SelectorRead.Scratch])).trans input.dimension) ((keepReg 47 (by simp [SelectorRead.Scratch])).trans input.digits)
      ((keepReg 48 (by simp [SelectorRead.Scratch])).trans input.count) ((keepReg 49 (by simp [SelectorRead.Scratch])).trans input.edgeWidth)
      rowRoom digitRoom separate (back ▸ sumRoom)
    obtain ⟨es,z,mz,rr,charge,post⟩ := run
    refine ⟨es,z,mz,rr,charge,⟨⟨fun j => ?_,fun a ha hd => (post.2.2 a ha hd).trans (congrFun back a)⟩,?_⟩⟩
    · simpa only [contribution,selection_of_stored stored,back] using post.1 j
    · intro j hj
      have stable : ∀ j : Reg, j.val < 41 → RowAccum.packetFromSelector.keeps j = true := by decide
      have untouched := stable j hj
      have outside : ¬SelectorRead.Scratch j := by
        rintro (rfl|rfl|rfl|rfl|rfl|rfl) <;> norm_num at hj
      exact (congrArg Fin.val (rr.keepsReg untouched)).trans ((keepReg j outside).trans (low j hj))
  refine ⟨complete,?_⟩
  intro es t mt rr
  obtain ⟨_,_,_,_,_,su,rest⟩ := Runs.seq_iff.mp rr
  obtain ⟨_,_,_,_,_,sr,_⟩ := Runs.seq_iff.mp rest
  obtain ⟨_,hm,low,input⟩ := (first.asTest (by decide)).sound su
  have good := ((second _ _ hm low input).sound sr).1
  change SelectorRead.Valid (readings _) _ _ _ at good
  change readings _ = mem at hm
  rw [hm] at good
  have pass : ok := good
  exact ⟨pass,((complete pass).asTest (by decide)).sound rr |>.2⟩

end Cube.PacketTally

end BorderVNP
end Computability
end OAI
