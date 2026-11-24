import OAI.Computability.VPVNP.CompressorShrinkSliceArrays
import OAI.Computability.VPVNP.CompressorTermRecordScan
import OAI.Computability.VPVNP.CompressorSlotOwnerDecode
import OAI.Computability.VPVNP.PackedShrinkStep

/-!
# Physical slice records of the six-party shrinking kernel

AB reads use the two bundle numberings at both endpoints. Surviving wires
use the selected payload-plus-selector width and the fixed subdivision count
of their role edge. The live frame stores the source offset, target offset
and length used by the local kernel.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceArrays

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.PackingData
open SliceSchedule

variable {w : ℕ}

theorem fieldAt_ordered {A : Type*} {n : ℕ} (order : A ≃ Fin n) (width : A → ℕ) (a : A) :
    fieldAt (orderedWidths order width) (order a).val = numberedField order width a := by
  simp [fieldAt,orderedWidths,numberedField,fieldStart,← Fin.ofFn_take_eq_take_ofFn (order a).isLt.le,
    List.sum_ofFn,Fin.take]

private theorem sliceAt_pair (old new : List ℕ) (i : ℕ) (j : Fin new.length) :
    sliceAt old new (i*new.length+j.val) =
      let s := fieldAt old i
      let t := fieldAt new j.val
      copySlice s.start s.width t.start t.width := by
  have hd : (i*new.length+j.val) / new.length = i := by
    rw [Nat.mul_comm i, Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt), Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  simp [sliceAt,pairAt,hd,Nat.mul_add_mod_of_lt j.isLt]

section Bundle

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c)
variable (number : P.BundleNumbering) (order : P.ThickNumbering) (width : Arc V H Tag L d c → ℕ)
variable (b : Site V Tag L × Fin d)

/-- The old array uses the rank among thick wires, the new array the rank
among CD motifs assigned to this bundle. -/
def thickWidths := orderedWidths (order b) (fun a : P.ThickFiber b => width a.1.1)
/-- AB piece widths of one bundle listed in its motif numbering, the order used to compute the
target offsets of the thick-wire slices. -/
def abWidths := orderedWidths (number b) (fun m : P.MotifFiber b => P.abWidth number width m.1)

theorem thickWidths_sum : (thickWidths P order width b).sum = P.bundleWidth width b := by
  rw [thickWidths,orderedWidths,List.sum_ofFn,bundleWidth]
  exact (order b).symm.sum_comp (fun a : P.ThickFiber b => width a.1.1)

theorem abWidths_split :
    abWidths P number width b = List.ofFn (splitWidth (P.bundleWidth width b) (pieceCount d c)) := by
  unfold abWidths orderedWidths
  congr 1
  funext i
  let m := (number b).symm i
  have he : P.abWidth number width m.1 =
      splitWidth (P.bundleWidth width b) (pieceCount d c) (number b m) := by
    obtain ⟨z,h⟩ := m
    subst b
    rfl
  simpa only [m,Equiv.apply_symm_apply] using he

/-- Consume both sorted width rows of a real packed bundle. -/
theorem ab_build (hc : 2 ≤ c) (hd : 0 < d) (o t B : Word w) (mem : Memory w)
    (space : Workspace o t B (2^c*d/4) (pieceCount d c)) (fit : P.bundleWidth width b < 2^w)
    (thick : ∀ i, (mem (o.val+i.val)).val = width (((order b).symm i).1.1))
    (ab : ∀ j, (mem (t.val+j.val)).val = P.abWidth number width (((number b).symm j).1)) :
    ∃ rs, Built o t B (thickWidths P order width b) (abWidths P number width b) mem rs := by
  apply build_arrays
  · simpa [thickWidths,abWidths,orderedWidths] using space
  · rw [thickWidths_sum]; exact fit
  · rw [abWidths,orderedWidths,List.sum_ofFn, (number b).symm.sum_comp (fun z : P.MotifFiber b => P.abWidth number width z.1),
      P.sum_abWidth hc hd number width b]; exact fit
  · intro i hi
    simpa [thickWidths,orderedWidths] using thick ⟨i,by simpa [thickWidths,orderedWidths] using hi⟩
  · intro j hj
    simpa [abWidths,orderedWidths] using ab ⟨j,by simpa [abWidths,orderedWidths] using hj⟩

/-- From only a sorted thick row and its computed total, construct the AB
pieces and both incidence directories, preserving the exact local cost. -/
theorem ab_build_from_total (q total o t B : Word w) (mem : Memory w)
    (count : q.val = pieceCount d c) (pos : 0 < q.val)
    (space : Workspace o t B (2^c*d/4) q.val)
    (apart : total.val < t.val ∨ t.val+q.val ≤ total.val)
    (rowsApart : o.val+2^c*d/4 ≤ t.val ∨ t.val+q.val ≤ o.val)
    (thick : ∀ i, (mem (o.val+i.val)).val = width (((order b).symm i).1.1))
    (sum : (mem total.val).val = P.bundleWidth width b) :
    ∃ split desc, SplitPass total q t mem split ∧
      Built o t B (thickWidths P order width b) (abWidths P number width b) (after mem (eventLog split)) desc := by
  let old := thickWidths P order width b
  have len : old.length = 2^c*d/4 := List.length_ofFn
  have src (i : ℕ) (hi : i < old.length) : (mem (o.val+i)).val = old[i] := by
    simpa only [old,thickWidths,orderedWidths,List.getElem_ofFn] using thick ⟨i,len ▸ hi⟩
  obtain ⟨rs,ds,run,built⟩ := split_build o total q t B old mem (len ▸ space) pos apart (len ▸ rowsApart)
    src (sum.trans (thickWidths_sum P order width b).symm)
  refine ⟨rs,ds,run,?_⟩
  rw [congrArg (fun n => List.ofFn (splitWidth old.sum n)) count] at built
  simpa only [old,thickWidths_sum,abWidths_split] using built

/-- The frame selected by the rank pair is the typed AB copy slice. -/
theorem ab_sliceAt (a : P.ThickFiber b) (m : P.MotifFiber b) :
    sliceAt (thickWidths P order width b) (abWidths P number width b)
      ((order b a).val * pieceCount d c + (number b m).val) = P.demandSlice number order width b a m := by
  let old := thickWidths P order width b
  let new := abWidths P number width b
  have hn : new.length = pieceCount d c := List.length_ofFn
  change sliceAt old new _ = _
  rw [congrArg (fun k => (order b a).val*k+(number b m).val) hn.symm]
  have pair := sliceAt_pair old new (order b a).val ⟨(number b m).val,lt_of_lt_of_eq (number b m).isLt hn.symm⟩
  rw [pair]
  simp only [old,new,thickWidths,abWidths,fieldAt_ordered,numberedField,demandSlice]

/-- The physical offset and length words implement the AB demand-bit bijection.
This characterizes both local A and local B reads, even when a field is empty. -/
theorem ab_stored_bits (hc : 2 ≤ c) (hd : 0 < d) {B : Word w} {prior mem : Memory w}
    (s : Stored B (thickWidths P order width b) (abWidths P number width b) prior mem)
    (a : P.ThickFiber b) (m : P.MotifFiber b) (i : Fin (width a.1.1))
    (j : Fin (P.abWidth number width m.1)) :
    let id := (order b a).val * pieceCount d c + (number b m).val
    let frame := frameHead B.val (2^c*d/4) (pieceCount d c) + 3*id
    P.demandBitEquiv hc hd number order width b ⟨m,j⟩ = ⟨a,i⟩ ↔
      ∃ k < (mem (frame+2)).val, i.val = (mem frame).val+k ∧ j.val = (mem (frame+1)).val+k := by
  intro id frame
  have hm : (thickWidths P order width b).length = 2^c*d/4 := List.length_ofFn
  have hn : (abWidths P number width b).length = pieceCount d c := List.length_ofFn
  have hi : id < (thickWidths P order width b).length * (abWidths P number width b).length := by
    rw [hm,hn]
    dsimp only [id]
    calc
      _ < (order b a).val * pieceCount d c + pieceCount d c :=
        Nat.add_lt_add_left (number b m).isLt _
      _ = ((order b a).val+1) * pieceCount d c := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (order b a).isLt
  have eqn := ab_sliceAt P number order width b a m
  have len := s.lengths id hi
  rw [hm,hn,eqn] at len
  change (mem (frame+2)).val = _ at len
  rw [len,P.demandBitEquiv_eq_iff_slice number order width b hc hd]
  dsimp only
  by_cases hz : 0 < (P.demandSlice number order width b a m).length
  · obtain ⟨src,dst⟩ := s.offsets id hi (eqn ▸ hz)
    rw [hm,hn,eqn] at src dst
    change (mem frame).val = _ at src
    change (mem (frame+1)).val = _ at dst
    rw [src,dst]
  · have zero : (P.demandSlice number order width b a m).length = 0 := by omega
    simp [zero]

end Bundle


/-- A singleton supply word intersects each subdivision in that entire
subdivision. Its local source offset is the sum of preceding widths. -/
theorem surviving_sliceAt (b q : ℕ) (hq : 0 < q) (j : Fin q) :
    let ws := List.ofFn (splitWidth b q)
    sliceAt [b] ws j.val = ⟨(ws.take j.val).sum,0,splitWidth b q j⟩ := by
  intro ws
  have hj : j.val < ws.length := by simp [ws]
  have hn : ws.sum = b := List.sum_ofFn.trans (sum_splitWidth _ _ hq)
  have hval : ws[j.val] = splitWidth b q j := List.getElem_ofFn ..
  have hsum := congrArg List.sum (List.take_append_drop (j.val+1) ws)
  rw [List.sum_append,List.sum_take_succ _ _ hj,hval,hn] at hsum
  have hbound : (ws.take j.val).sum + splitWidth b q j ≤ b := by omega
  have pair := sliceAt_pair [b] ws 0 ⟨j.val,hj⟩
  simp only [Nat.zero_mul,Nat.zero_add] at pair
  rw [pair]
  simp [fieldAt,copySlice,hj,hval,Nat.min_eq_right hbound]

/-- The target width, copied length and offsets left by the descriptor builder
are the word sections consumed by the source and target role maps. -/
theorem surviving_frame (b q : ℕ) (hq : 0 < q) {B : Word w} {prior mem : Memory w}
    (stored : Stored B [b] (List.ofFn (splitWidth b q)) prior mem) (j : Fin q) :
    let frame := frameHead B.val 1 q + 3*j.val
    (mem (frame+2)).val = splitWidth b q j ∧
    ∀ k : Fin (splitWidth b q j), (mem (frame+1)).val = 0 ∧
      (mem frame).val+k.val = (ShrinkPayload.sliceBits b q hq ⟨j,k⟩).val := by
  intro frame
  let ws := List.ofFn (splitWidth b q)
  have hj : j.val < [b].length*ws.length := by simp [ws]
  have eqn := surviving_sliceAt b q hq j
  have hlen := stored.lengths j.val hj
  rw [eqn] at hlen
  refine ⟨by simpa only [List.length_singleton,List.length_ofFn,frame] using hlen,?_⟩
  intro k
  have hp : 0 < (sliceAt [b] ws j.val).length := by rw [eqn]; exact Nat.zero_lt_of_lt k.isLt
  obtain ⟨h₁,h₂⟩ := stored.offsets j.val hj hp
  rw [eqn] at h₁ h₂
  simp only [List.length_singleton,List.length_ofFn] at h₁ h₂
  refine ⟨h₂,?_⟩
  rw [show (mem frame).val = (ws.take j.val).sum from h₁,ShrinkPayload.sliceBits_offset]
  simp [ws,← Fin.ofFn_take_eq_take_ofFn j.isLt.le,List.sum_ofFn,Fin.take]

section Surviving

open MotifGrid MotifBlocks MotifConversion MotifDemandPadding ShrinkMotif

variable {V H Tag L : Type} {d c N J nL : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c) (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)
variable {K : Type*} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass)
  (31 / 16) factor)
variable (number : P.BundleNumbering) (old : Arc V H Tag L d c → ℕ)
variable (choice : ∀ m : P.Motif, P.ShrinkChoice number old F m)

/-- The fixed order of the two groups of four supply roles, as in the term reader. -/
def supplyRoles : Fin 8 ≃ Bool × Fin 4 :=
  (finProdFinEquiv (m := 2) (n := 4)).symm.trans (finTwoEquiv.prodCongr (Equiv.refl (Fin 4)))

theorem supplyRoles_index (l : Bool) (t : Fin 4) :
    (supplyRoles.symm (l,t)).val = l.toNat*4+t.val := by
  change t.val + 4 * (finTwoEquiv.symm l).val = l.toNat*4+t.val
  cases l <;> simp [Nat.add_comm]

/-- Rectangular width rows indexed by absolute CD arc, role type and
subdivision. The larger common stride admits direct addressing for every role. -/
def survivingRowBase (widthBase : ℕ) (subdiv : Fin 4 → ℕ) (m : P.Motif) (t : Fin 4) : ℕ :=
  widthBase + ((Slots.oldArcIndex P vertices tags lanes m.val).val * 4 + t.val) * ∑ e, subdiv e

/-- The whole term scan supplies all fields needed to reconstruct its image in
one row; earlier input memories and the saved headers need not be retained. -/
theorem fields_record {n : ℕ} {E : Type} (supply : Fin n ≃ E) (v : E → ℕ)
    (m : Memory w) (base : Word w) (fit : base.val+2+n < 2^w)
    (fields : ∀ i, (m (base.val+2+i.val)).val = v (supply i)) :
    ∀ x, base.val ≤ x → x < base.val+2+n → m x =
      TermRecord.recordMemory m base (m base.val) (m (base.val+1)) supply v x := by
  obtain ⟨hr,hu,hv,_⟩ := TermRecord.recordMemory_fields m base (m base.val) (m (base.val+1)) supply v fit
  intro x hlo hhi
  by_cases h₀ : x = base.val
  · simpa only [h₀] using hr.symm
  by_cases h₁ : x = base.val+1
  · simpa only [h₁] using hu.symm
  let i : Fin n := ⟨x-(base.val+2),by omega⟩
  have hi : x = base.val+2+i.val := by dsimp [i]; omega
  rw [hi,hv i]
  apply Fin.ext
  rw [Fin.val_natCast,← fields i,Nat.mod_eq_of_lt (m _).isLt]

/-- A row read from the selected six-party term is written at the physical
address decoded by the new-slot scan. Both lists of slice references and the
widths survive the descriptor pass. -/
theorem surviving_build (subdiv : Fin 4 → ℕ) (m : P.Motif) (layout : Bool) (t : Fin 4)
    (mem : Memory w) (term total B : Word w) (widthBase : ℕ)
    (recFit : term.val+2+8 < 2^w) (cap : outerCap F (P.shrinkDemandWidths number old m) < 2^w)
    (fields : TermRecordScan.Fields F supplyRoles demandMass_pos (P.shrinkDemandWidths number old m)
      (choice m).val term mem)
    (selectors : F.selectorBits < 2^w) (wf : P.termWidths F number old choice m layout t < 2^w)
    (hc : 0 < subdiv t) (hcount : subdiv t < 2^w)
    (hbase : survivingRowBase P vertices tags lanes widthBase subdiv m t < 2^w)
    (space : Workspace total (Fin.ofNat _ (survivingRowBase P vertices tags lanes widthBase subdiv m t))
      B 1 (subdiv t))
    (apart : total.val < survivingRowBase P vertices tags lanes widthBase subdiv m t ∨
      survivingRowBase P vertices tags lanes widthBase subdiv m t + subdiv t ≤ total.val) :
    let dst : Word w := Fin.ofNat _ (survivingRowBase P vertices tags lanes widthBase subdiv m t)
    let q : Word w := Fin.ofNat _ (subdiv t)
    let width := P.termWidths F number old choice m layout t
    let pub := supplyData (Fin.ofNat _ (layout.toNat*4+t.val)) (Fin.ofNat _ F.selectorBits) total
    let r := supplyReport pub term mem
    let prog := (template supplyOps 0).instantiate w pub
    let mid := after mem r.events
    execute prog.program 16 (prog.program.start term) mem [] = some r ∧ (mid total.val).val = width ∧
      ∃ split desc, SplitPass total q dst mid split ∧
        Built total dst B [width] (List.ofFn (splitWidth width (subdiv t))) (after mid (eventLog split)) desc ∧
        let out := desc.result (after mid (eventLog split))
        (∀ j : Fin (subdiv t), (out (widthBase+((Slots.oldArcIndex P vertices tags lanes m.val).val*4+t.val) *
          (∑ e, subdiv e)+j.val)).val = splitWidth width (subdiv t) j) ∧
        ∀ x, x ≠ total.val → (x < dst.val ∨ dst.val+subdiv t ≤ x) →
          (x < B.val ∨ stop B.val 1 (subdiv t) ≤ x) → out x = mem x := by
  intro dst q width pub r prog mid
  let i := supplyRoles.symm (layout,t)
  have hd : dst.val = survivingRowBase P vertices tags lanes widthBase subdiv m t := Nat.mod_eq_of_lt hbase
  have hq : q.val = subdiv t := Nat.mod_eq_of_lt hcount
  have hs : supplyRoles i = (layout,t) := supplyRoles.apply_symm_apply _
  have hwidth : supplyWidths F (P.shrinkDemandWidths number old m) (choice m).val (supplyRoles i) = width := by
    rw [hs]; rfl
  have hp : supplyData (Fin.ofNat _ i.val) (Fin.ofNat _ F.selectorBits) total = pub := by
    rw [show i.val = _ from supplyRoles_index layout t]
  obtain ⟨run,hw,_,_,split,desc,pass,built⟩ := supply_build F supplyRoles supplyMass_pos
    (P.shrinkDemandWidths number old m) (choice m) i mem mem term (mem term.val) (mem (term.val+1)) q total dst B recFit cap fields.2.1
    (fields_record supplyRoles (choice m).val mem term recFit fields.2.2) selectors (hwidth ▸ wf) (hq ▸ space) (hq ▸ hc) (by simpa only [hd,hq] using apart)
  simp only [hp,hwidth] at run hw pass built
  have eqWidths := congrArg (fun n => List.ofFn (splitWidth width n)) hq
  rw [eqWidths] at built
  refine ⟨run,hw,split,desc,pass,built,?_,?_⟩
  · intro j
    have hi : j.val < q.val := lt_of_lt_of_eq j.isLt hq.symm
    have raw := pass.widths.rows ⟨j.val,hi⟩ hi
    change (after mid (eventLog split) (dst.val+j.val)).val = splitWidth (mid total.val).val q.val ⟨j.val,hi⟩ at raw
    have he : splitWidth width q.val ⟨j.val,hi⟩ = splitWidth width (subdiv t) j := by
      simp only [splitWidth,hq]
    rw [hw,he] at raw
    have outside := space.newApart
    have frame := built.stored.outside (dst.val+j.val) (by
      simp only [List.length_singleton,List.length_ofFn]; change dst.val+subdiv t ≤ B.val ∨ stop B.val 1 (subdiv t) ≤ dst.val at outside
      have := j.isLt; omega)
    rw [← frame,hd] at raw
    exact raw
  · intro x ht hd' hb
    rw [built.stored.outside x (by simpa only [List.length_singleton,List.length_ofFn] using hb),
      pass.widths.frame x (show x < dst.val ∨ dst.val+q.val ≤ x by simpa only [hq] using hd')]
    rw [(supply_native pub term mem).2.1,writeMemory,show pub 2 = total from rfl,ite_eq_right ht]

end Surviving

end CompressorRecords.ShrinkSliceArrays

end VPVNP
end Computability
end OAI
