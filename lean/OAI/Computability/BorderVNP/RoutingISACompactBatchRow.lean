import OAI.Computability.BorderVNP.RoutingISACompactBatchModel
import OAI.Computability.BorderVNP.RoutingISAExternalSeed
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Reading and executing one packed cell-preparation task -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactBatch

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM Packing.Directory.ISA

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Actual seed writes establish all payload bits in scratch memory and retain the suffix. -/
theorem Task.source_after_seed (t : Task) (m : Memory w) (hw : 0 < w) (input : t.Input m) :
    CompactWrite.Source (t.seed m) t.scratch t.payload := by
  intro j hj
  let bs := CompactMachine.externalRecords t.external
  let digits := bs.map (fun b => DiagonalResidueRAM.word w b.toNat)
  have len : digits.length = bs.length := List.length_map ..
  change j < (bs ++ t.suffix).length at hj
  change (putWords m t.scratch digits (t.scratch+j)).val = (bs++t.suffix)[j].toNat
  by_cases left : j < bs.length
  · let p : Fin digits.length := ⟨j,len ▸ left⟩
    have h := putWords_read m t.scratch digits p
    change putWords m t.scratch digits (t.scratch+j) = digits[j] at h
    rw [h, List.getElem_append_left left]
    simp only [digits, List.getElem_map]
    apply DiagonalResidueRAM.word_val
    have hh := Nat.one_lt_two_pow hw.ne'
    have hbit := (bs[j]).toNat_le
    omega
  · have le : bs.length ≤ j := by omega
    have pos : j-bs.length < t.suffix.length := by simp only [List.length_append] at hj; omega
    rw [putWords_outside m t.scratch (t.scratch+j) digits (Or.inr (by omega)), List.getElem_append_right le]
    have h := input.2 _ pos
    have hlen : bs.length = 12*t.external.length := CompactMachine.length_externalRecords _
    rwa [show t.scratch+12*t.external.length+(j-bs.length) = t.scratch+j by omega] at h

private theorem kept {table count i : ℕ} {s m es t mt} {c : Code} (r : Runs pub macros c s m es t mt)
    (h : Ready table count i s)
    (h39 : c.keeps 39 = true) (h2 : c.keeps 2 = true) (h32 : c.keeps 32 = true)
    (h33 : c.keeps 33 = true) (h34 : c.keeps 34 = true) (h35 : c.keeps 35 = true) :
    Ready table count i t := by
  simpa only [Ready,r.keepsReg h39,r.keepsReg h2,r.keepsReg h32,r.keepsReg h33,
    r.keepsReg h34,r.keepsReg h35] using h

private theorem fetch_run {table count i : ℕ} (a : Task) (s : Bank w) (m : Memory w)
    (ready : Ready table count i s) (row : a.Stored m table i)
    (fits : table+5*count ≤ 2^w) (hi : i < count) :
    ∃ es t, Runs pub macros fetch s m es t m ∧ traceCost es ≤ fetch.slots ∧ Ready table count i t ∧
      (t 3).val = a.extBase ∧ (t 4).val = a.external.length ∧ (t 5).val = a.scratch ∧
      (t 37).val = a.payload.length ∧ (t 38).val = a.dest := by
  have control := ready
  obtain ⟨one,_,base,_,ix,stride⟩ := control
  change readings s 39 = 1 at one
  change readings s 32 = table at base
  change readings s 34 = i at ix
  change readings s 35 = 5 at stride
  have safe : fetch.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [fetch, Code.block, Code.safeReadOnly, Code.evalNat,
      addressOpFits,addressOp,base,ix,stride,one]
    omega
  obtain ⟨es,t,r,c,eq⟩ := fetch.runReadOnly pub macros m s safe
  obtain ⟨h0,h1,h2,h3,h4⟩ := row
  refine ⟨es,t,r,c,kept r ready (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),?_⟩
  change readings t 3 = _ ∧ readings t 4 = _ ∧ readings t 5 = _ ∧ readings t 37 = _ ∧ readings t 38 = _
  rw [eq]
  simp (config := {decide := true}) [fetch, Code.block, Code.evalNat, addressOp,base,ix,stride,one]
  exact ⟨h0,h1,h2,h3,h4⟩

private theorem move_run (s : Bank w) (m : Memory w) :
    ∃ t, Runs pub macros move s m [tick w,tick w,tick w] t m ∧ t 3=s 5 ∧ t 4=s 37 ∧ t 5=s 38 := by
  let a := Function.update s 3 (s 5)
  let b := Function.update a 4 (a 37)
  let c := Function.update b 5 (b 38)
  have h : Runs pub macros (.copy 3 5) s m [tick w] a m := .localStep m rfl rfl
  have j : Runs pub macros (.copy 4 37) a m [tick w] b m := .localStep m rfl rfl
  have k : Runs pub macros (.copy 5 38) b m [tick w] c m := .localStep m rfl rfl
  exact ⟨_,h.seq (j.seq k),by simp (config := {decide := true}) [c,b,a]⟩

/-- The actual table read and two writers complete one task, preserve the high control
registers, and advance the loop cursor. The bound charges the seed and payload lengths separately. -/
theorem body_run {table count i : ℕ} (a : Task) (s : Bank w) (m : Memory w) (hw : 0 < w)
    (ready : Ready table count i s) (hi : i < count) (room : table+5*count ≤ 2^w)
    (row : a.Stored m table i) (input : a.Input m) (fit : a.Fits w) :
    ∃ es u, Runs pub macros body s m es u (a.write m) ∧ traceCost es ≤ a.cost ∧ Ready table count (i+1) u := by
  obtain ⟨xs,x,fr,fc,hx,x3,x4,x5,x37,x38⟩ := fetch_run (pub := pub) (macros := macros) a s m ready row room hi
  obtain ⟨ys,y,seed,sc,_⟩ := ExternalSeed.writer_runs (pub := pub) (macros := macros)
    x m a.external hw x3 x4 x5 input.1 fit.extSeparate fit.ext fit.prefixFit
  have hy : Ready table count i y :=
    kept seed hx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z,mv,z3,z4,z5⟩ := move_run (pub := pub) (macros := macros) y (a.seed m)
  have hz := kept mv hy (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have k (j : Reg) (hj : ExternalSeed.writer.keeps j = true) : y j = x j := seed.keepsReg hj
  have bs : (z 3).val = a.scratch := (congrArg Fin.val (z3.trans (k 5 (by decide)))).trans x5
  have bl : (z 4).val = a.payload.length := (congrArg Fin.val (z4.trans (k 37 (by decide)))).trans x37
  have bd : (z 5).val = a.dest := (congrArg Fin.val (z5.trans (k 38 (by decide)))).trans x38
  obtain ⟨zs,v,pack,pc⟩ := CompactWrite.writer_runs (pub := pub) (macros := macros) z (a.seed m)
    a.payload hw hz.2.1 bs bl bd (a.source_after_seed m hw input) fit.packSeparate fit.scratch fit.dest
  have hv := kept pack hz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let u := Function.update v 34 (BinaryOp.add.eval (v 34) (v 39))
  have inc : Runs pub macros (.binary .add 34 34 39) v (a.write m) [tick w] u (a.write m) := .localStep _ rfl rfl
  refine ⟨_,u,fr.seq (seed.seq (mv.seq (pack.seq inc))),?_,?_⟩
  · simp only [traceCost, VPVNP.RAMBuckets.cost_append] at *
    change _ + (_ + (3+(_+1))) ≤ a.cost
    unfold Task.cost
    change _ ≤ _ + 3 + _ + _ + 2 + 1
    omega
  · obtain ⟨one,width,base,size,index,stride⟩ := hv
    have bound := size.symm.trans_lt (v 33).isLt
    simp (config := {decide := true}) [Ready,u,BinaryOp.eval,Fin.val_add,one,width,base,size,index,
      stride,Nat.mod_eq_of_lt (by omega : i+1 < 2^w)]

end RoutingISA.CompactBatch

end BorderVNP
end Computability
end OAI
