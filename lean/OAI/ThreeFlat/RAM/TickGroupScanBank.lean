import OAI.ThreeFlat.RAM.TickGroupScanROM
import OAI.ThreeFlat.RAM.TickChunkCheck
import OAI.ThreeFlat.RAM.TickCheckedBank
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # A single relocatable ROM bank for the history scan phase -/

namespace ThreeFlat.RAM.TickGroupScanBank

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr TickGroupScanSetup TickIntervalCursor
open TickChunkCheck Diagonal.TickGroupIntervals ChunkRequests TickBitRelation
open scoped Classical Fin.CommRing

variable {w k p r : ℕ} {F : Type*} [Semiring F]

/-- The actual scan branch starts by loading its pointers from the tick cache
and exits to the selected common continuation. No interpreter step is abstract. -/
theorem mass (field : FieldCode F w) (M : Machine w p r k) (A : Plan)
    (P : Labels w k A ↪ Fin p) (regs : Fin 15 ↪ Fin r) (gen : Fin (4+(expr w k A).binds) ↪ Fin r)
    (chk : Fin 37 ↪ Fin r) (next : Fin p) (rom : ∀ i, M.code (P i) = emit A P regs gen chk next i)
    (es : List Interval) (disj : es.Pairwise Compatible) (lo g : ℕ)
    (c : Config w p r) (m : Memory w) (entry : c.pc = boot A P 0)
    (nread : m (A.countAddr : Word w).val = (es.length : Word w))
    (lread : m (A.chunkAddr : Word w).val = (lo : Word w))
    (gread : m (A.groupAddr : Word w).val = (g : Word w))
    (space : (layout A lo g).Fits w) (width : 64 ≤ 2^w)
    (tableFit : A.table+4*es.length < 2^w) (endFit : A.reqStart+8*A.bits < 2^w)
    (good : ∀ e ∈ es, FitsRow e w) (stored : Stores m A.table es)
    (separate : ∀ x, A.table ≤ x → x < A.table+4*es.length → x < A.mapBase ∨ A.mapBase+A.bits ≤ x)
    (zeros : ∀ j < A.bits, m (A.mapBase+j) = 0)
    (codeFit : ∀ i : Fin (chunkSize (layout A lo g)), codeAt (layout A lo g) es i.val < 2^w)
    (mapSafe : ∀ i : Fin (chunkSize (layout A lo g)), outside A.reqStart A.bits ((A.mapBase : Word w)+(i.val : Word w)).val)
    (op np : ℕ → Bool)
    (oldPair : PairReads (output (layout A lo g) m es) A.reqStart (layout A lo g) es A.oldPtr op)
    (newPair : PairReads (output (layout A lo g) m es) A.reqStart (layout A lo g) es A.newPtr np)
    (x y : Fin (chunkSize (layout A lo g)) → Bool)
    (oldOutside : ∀ i : Fin (chunkSize (layout A lo g)), ((A.old : Word w)+(i.val : Word w)).val < A.reqStart)
    (newOutside : ∀ i : Fin (chunkSize (layout A lo g)), ((A.new : Word w)+(i.val : Word w)).val < A.reqStart)
    (old_ok : ∀ i : Fin (chunkSize (layout A lo g)), bitAt (output (layout A lo g) m es) (A.old : Word w)
      (i.val : Word w) = bitWord w (x i))
    (new_ok : ∀ i : Fin (chunkSize (layout A lo g)), bitAt (output (layout A lo g) m es) (A.new : Word w)
      (i.val : Word w) = bitWord w (y i)) :
    let L := layout A lo g
    let saved := fillSegment A.reqStart (8*A.bits) (TickRequestStream.dataWord A.reqStart
      (rules true L es op np)) (output L m es)
    ∃ t ≤ 29+20*es.length+4319*A.bits, ∃ out : Config w p r, out.pc = next ∧
      ∀ fuel, RAM.mass field M.program (fuel+t) c m = if valid true L es op np x y
        then RAM.mass field M.program fuel out saved else 0 := by
  dsimp only
  let L := layout A lo g
  have len : chunkSize L = A.bits := size A lo g
  let E := expr w k A
  have rowBase : L.mapBase = A.mapBase := rfl
  let C := checked A P
  have terms : TickCheckedBank.Installed M E (A.reqStart : Word w) (A.reqStart+8*A.bits : ℕ)
      (A.old : Word w) (A.new : Word w) C gen chk next :=
    ⟨fun i => rom (.inr (.inr i))⟩
  have table : TickIntervalCursor.Installed M (cursor A P) regs (checkEntry A P) := fun i => rom (.inr (.inl i))
  obtain ⟨b,pre,bpc,base,last,low,high,map,grp⟩ := TickGroupScanSetup.advance_setup A.toAddresses M
    (boot A P) regs (cursor A P 0) (fun i => rom (.inl i)) c m entry
  rw [nread] at last
  rw [lread] at low high
  rw [gread] at grp
  have stop : b.reg (regs 1) = ((A.table+4*es.length : ℕ) : Word w) := by
    rw [last,Nat.cast_add,Nat.cast_mul]
    simp only [Nat.cast_ofNat,mul_comm]
  have high' : b.reg (regs 3) = (L.chunkEnd : Word w) := by
    change _ = ((lo+A.bits : ℕ) : Word w)
    rwa [Nat.cast_add]
  have sep : ∀ x, A.table ≤ x → x < A.table+4*es.length →
      x < L.mapBase ∨ L.mapBase+chunkSize L ≤ x := by simpa only [len,rowBase] using separate
  let saved := fillSegment A.reqStart (8*A.bits) (TickRequestStream.dataWord A.reqStart
    (rules true L es op np)) (output L m es)
  have body (d : Config w p r) (here : d.pc = checkEntry A P) :
      ∃ t ≤ 14+4314*chunkSize L, ∃ out : Config w p r, out.pc = next ∧ ∀ fuel,
        RAM.mass field M.program (fuel+t) d (output L m es) = if valid true L es op np x y
          then RAM.mass field M.program fuel out saved else 0 := by
    obtain ⟨t,bd,out,done,sem⟩ := mass_chunk field M true L space es disj A.reqStart A.oldPtr A.newPtr
      op np (A.old : Word w) (A.new : Word w) x y d m width (by simpa only [len] using endFit)
      (TickCheckedBank.generatePC E C) gen (TickCheckedBank.setupPC E C) (linkedRegisters w k chk)
      (linkedLabels w k (TickCheckedBank.scanPC E C)) _ _ _ next
      (by
        intro i
        change M.code (TickCheckedBank.generatePC E C i) =
          TickGenerateTable.emit E (A.reqStart : Word w) ((A.reqStart + 8 * chunkSize L : ℕ) : Word w)
            (TickCheckedBank.generatePC E C) gen (TickCheckedBank.setupPC E C 0) i
        rw [len]
        exact terms.gen i) (by simpa only [len] using terms.setup) terms.check here
      (fun _ => ⟨by simpa only [len,rowBase] using zeros,codeFit,by simpa only [len,rowBase] using mapSafe,oldPair,newPair⟩)
      oldOutside newOutside old_ok new_ok
    exact ⟨t,bd.trans (TickChunkCheck.cost_le ..),out,done,fun f => by simpa only [len,saved] using sem f⟩
  obtain ⟨t,bd,out,done,sem⟩ := with_intervals field M (cursor A P) regs (checkEntry A P) next table
    L space es disj A.table tableFit good b m bpc stored base stop low high' map grp sep
    saved (valid true L es op np x y) body
  refine ⟨13+t,by rw [len] at bd; omega,out,done,?_⟩
  intro fuel
  rw [show fuel+(13+t) = (fuel+t)+13 by omega]
  exact (mass_of_advance field M.program pre (fuel+t)).trans (sem fuel)

/-- All decoded cache, layout, interval, and mounted-pin facts for one physical
scan. They are independent of the native program, registers, and fuel. -/
structure ScanInputs (w : ℕ) (A : Plan) (es : List Interval) (lo g : ℕ) (m : Memory w)
    (op np : ℕ → Bool) (x y : Fin (chunkSize (layout A lo g)) → Bool) : Prop where
  disj : es.Pairwise Compatible
  nread : m (A.countAddr : Word w).val = (es.length : Word w)
  lread : m (A.chunkAddr : Word w).val = (lo : Word w)
  gread : m (A.groupAddr : Word w).val = (g : Word w)
  space : (layout A lo g).Fits w
  width : 64 ≤ 2^w
  tableFit : A.table+4*es.length < 2^w
  endFit : A.reqStart+8*A.bits < 2^w
  good : ∀ e ∈ es, FitsRow e w
  stored : Stores m A.table es
  separate : ∀ x, A.table ≤ x → x < A.table+4*es.length → x < A.mapBase ∨ A.mapBase+A.bits ≤ x
  zeros : ∀ j < A.bits, m (A.mapBase+j) = 0
  codeFit : ∀ i : Fin (chunkSize (layout A lo g)), codeAt (layout A lo g) es i.val < 2^w
  mapSafe : ∀ i : Fin (chunkSize (layout A lo g)), outside A.reqStart A.bits ((A.mapBase : Word w)+(i.val : Word w)).val
  oldPair : PairReads (output (layout A lo g) m es) A.reqStart (layout A lo g) es A.oldPtr op
  newPair : PairReads (output (layout A lo g) m es) A.reqStart (layout A lo g) es A.newPtr np
  oldOutside : ∀ i : Fin (chunkSize (layout A lo g)), ((A.old : Word w)+(i.val : Word w)).val < A.reqStart
  newOutside : ∀ i : Fin (chunkSize (layout A lo g)), ((A.new : Word w)+(i.val : Word w)).val < A.reqStart
  old_ok : ∀ i : Fin (chunkSize (layout A lo g)), bitAt (output (layout A lo g) m es) (A.old : Word w)
      (i.val : Word w) = bitWord w (x i)
  new_ok : ∀ i : Fin (chunkSize (layout A lo g)), bitAt (output (layout A lo g) m es) (A.new : Word w)
      (i.val : Word w) = bitWord w (y i)

/-- The terminal history scan evaluates the exact physical pair guard at
every fuel above the stated bound. -/
theorem returns (field : FieldCode F w) (M : Machine w p r k) (A : Plan)
    (P : Labels w k A ↪ Fin p) (regs : Fin 15 ↪ Fin r)
    (gen : Fin (4+(expr w k A).binds) ↪ Fin r) (chk : Fin 37 ↪ Fin r)
    (next : Fin p) (rom : ∀ i, M.code (P i) = emit A P regs gen chk next i)
    (terminal : M.code next = .accept)
    (es : List Interval) (lo g : ℕ) (c : Config w p r) (m : Memory w)
    (op np : ℕ → Bool) (x y : Fin (chunkSize (layout A lo g)) → Bool)
    (entry : c.pc = boot A P 0) (input : ScanInputs w A es lo g m op np x y) :
    TickFuel.Returns field M.program (30+20*es.length+4319*A.bits) c m
      (if valid true (layout A lo g) es op np x y then 1 else 0) := by
  obtain ⟨t,bd,d,pc,sem⟩ := mass field M A P regs gen chk next rom es input.disj lo g c m entry
    input.nread input.lread input.gread input.space input.width input.tableFit input.endFit input.good
    input.stored input.separate input.zeros input.codeFit input.mapSafe op np input.oldPair input.newPair
    x y input.oldOutside input.newOutside input.old_ok input.new_ok
  let L := layout A lo g
  let saved := fillSegment A.reqStart (8*A.bits) (TickRequestStream.dataWord A.reqStart
    (rules true L es op np)) (output L m es)
  have last := TickFuel.accept (field:=field) M d saved (by rw [pc]; exact terminal)
  exact (TickFuel.Returns.guard _ sem last).later (by omega)



end ThreeFlat.RAM.TickGroupScanBank

end OAI
