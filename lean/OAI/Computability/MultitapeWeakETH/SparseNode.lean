import OAI.Computability.MultitapeWeakETH.SparsePreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSInvariantSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement

/-! # A polynomial tape call identifying a sparse leaf or producing both disjoint children -/

namespace OAI.Computability.MultitapeWeakETH.SparsePreparation

open IntegerMultiplication Code Bits Strip Staff Carry StackInterpreter BitInterpreter
open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSProgram SparseDFSRefinement SparsePriorityProgram
open private records records_poly records_encode from OAI.Computability.MultitapeWeakETH.LeafSyntax
open scoped Classical
noncomputable section

attribute [local irreducible] StructuredCalls.compiled SparseDFSProgram.selectCurrent SparseDFSProgram.branch Selector.selectorCoefficient

private abbrev Request := Word × Word

private def seed (q : Request) : SparseDFSProgram.Data :=
  ⟨fun _ => false,fun i => if i=265 then q.2 else if i=259 then q.1 else if i=257 then [false] else []⟩

private theorem seed_poly : Poly (fun q => stateImage (seed q)) := by
  apply (Code.Poly.const (Label.mk (fun _ : Fin 80 => false))).pair (pack_poly (fun i q => (seed q).stacks i) _)
  intro i
  by_cases a : i=265
  · simpa [seed,a] using (Easy.snd (X:=Word) (Y:=Word)).poly
  by_cases b : i=259
  · simpa [seed,a,b] using (Easy.fst (X:=Word) (Y:=Word)).poly
  simpa [seed,a,b] using (Code.Poly.const (X:=Request) (if i=257 then [false] else []))

private def selectFuelAt (C : ℕ) (q : Request) :=
  tally (C*(q.2.length+q.1.length+1)^4+2)

private def branchFuelAt (C : ℕ) (q : Request) := tally (C*(4*q.2.length+3)^2+1)

private theorem selectFuel_poly (C : ℕ) : Poly (selectFuelAt C) := by
  change Realizes (tapeReg Request) (fun q => C*(q.2.length+q.1.length+1)^4+2)
  have body := word_length (Easy.snd (X:=Word) (Y:=Word)).poly
  have threshold := word_length (Easy.fst (X:=Word) (Y:=Word)).poly
  exact ((Realizes.fix C).times (unary_pow ((body.plus threshold).plus (Realizes.fix 1)) 4)).plus (Realizes.fix 2)

private theorem branchFuel_poly (C : ℕ) : Poly (branchFuelAt C) :=
  ((Realizes.fix C).times (unary_pow (((Realizes.fix 4).times
    (word_length (Easy.snd (X:=Word) (Y:=Word)).poly)).plus (Realizes.fix 3)) 2)).plus (Realizes.fix 1)

private def selected (C : ℕ) (q : Request) := call (selectCurrent 3) 256 (selectFuelAt C q,stateImage (seed q))

private def children (C D : ℕ) (q : Request) : Option (List Word) :=
  let after := selected C q
  bif after.1.val 23 then some (records (get (257 : Fin 1220) (call branch 256 (branchFuelAt D q,after)).2))
  else none

private theorem children_poly (C D : ℕ) : Poly (children C D) := by
  have sel : Poly (selected C) := ((selectFuel_poly C).pair seed_poly).compose (call_poly (selectCurrent 3) 256)
  have flag := sel.fstCompose.compose (Easy.finite (fun r : Label (Fin 80 → Bool) => r.val 23)).poly
  have run := ((branchFuel_poly D).pair sel).compose (call_poly branch 256)
  exact Poly.choose flag ((run.sndCompose.compose (get_easy (257 : Fin 1220)).poly).compose
    (records_poly.compose Easy.some.poly)) (Code.Poly.const none)


/-- Each nonterminal call returns exactly the two normalized children of
one permitted priority branch. Terminal calls certify the missing selector. -/
theorem split_program :
    ∃ split : Word × Word → Option (List Word), Poly split ∧
      ∀ {n : ℕ} (F : RawCNF n) (w : Word), Valid 3 F → 2 ≤ BinaryArithmetic.toNat w →
        let out := split (w,SparseCountProgram.encodeBody F)
        (out=none ∧ SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat w)=none) ∨
        ∃ c H, RawPriority 3 F (BinaryArithmetic.toNat w) c H ∧
          out=some [SparseCountProgram.encodeBody (childA F c H),SparseCountProgram.encodeBody (childB F c H)] := by
  refine ⟨children (Selector.selectorCoefficient 3) 621000,children_poly _ _,?_⟩
  intro n F w valid two out
  let q : Request := (w,SparseCountProgram.encodeBody F)
  let d := seed q
  have clean (i : Fin 1220) (h : i.val<24) : d.stacks i=[] := by
    have h1 : i ≠ 265 := by intro eq; subst i; contradiction
    have h2 : i ≠ 259 := by intro eq; subst i; contradiction
    have h3 : i ≠ 257 := by intro eq; subst i; contradiction
    simp [d,seed,h1,h2,h3]
  have cap (i : Fin 1220) : (d.stacks i).length ≤ q.1.length+q.2.length+1 := by
    dsimp only [d,seed]
    split <;> try omega
    split <;> try omega
    split <;> simp
  obtain ⟨t,ht,e,he,frame,miss,hit,_⟩ := SparseSelectorRefinement.selectCurrent_execution F w d _
    (by decide : 2 ≤ 3) two valid.width valid.literal_nodup valid.clause_nodup rfl rfl clean cap
  have scan : selected (Selector.selectorCoefficient 3) q = stateImage e := by
    unfold selected selectFuelAt
    apply call_eq _ _ he
    change t+1 ≤ Selector.selectorCoefficient 3*SparseSelectorRefinement.inputVolume F w ^ 4+2
    exact Nat.add_le_add_right ht 1
  change (children (Selector.selectorCoefficient 3) 621000 q=none ∧ _) ∨ _
  cases flag : e.regs 23 with
  | false =>
    refine Or.inl ⟨?_,(miss flag).2.2.2.1⟩
    simp only [children,scan,stateImage,flag,Bool.cond_false]
  | true =>
    obtain ⟨c,H,priority,_,hH,hS⟩ := hit flag
    let S := selectedRaw F c H
    have left := frame 261 (by decide) (by decide)
    have right := frame 262 (by decide) (by decide)
    obtain ⟨tb,hb,f,hf,pending,_⟩ := typed_branch_execution e F S H
      (frame 265 (by decide) (by decide)) hH hS left right
      (fun i hi h9 h12 => (frame i h9 h12).trans (clean i hi))
    have lim := SparseDFSInvariantSpace.selected_inputVolume_le F H priority.candidate
    have cost := hb.trans (Nat.mul_le_mul_left 621000 (Nat.pow_le_pow_left lim 2))
    have branchRun : call branch 256 (branchFuelAt 621000 q,stateImage e) = stateImage f := by
      apply call_eq _ _ hf
      exact Nat.add_le_add_right cost 1
    have before : e.stacks 257=[false] := frame 257 (by decide) (by decide)
    have after : f.stacks 257 = Encoding.encodeList SparseCountProgram.encodeBody [childA F c H,childB F c H] := by
      rw [pending,before]
      rfl
    refine Or.inr ⟨c,H,priority,?_⟩
    change children (Selector.selectorCoefficient 3) 621000 q = _
    simp only [children,scan,stateImage,flag,Bool.cond_true]
    change some (records (get (257 : Fin 1220) (call branch 256 (branchFuelAt 621000 q,stateImage e)).2)) = _
    rw [branchRun]
    simp [stateImage,get_pack,after,records_encode]

end
end OAI.Computability.MultitapeWeakETH.SparsePreparation
