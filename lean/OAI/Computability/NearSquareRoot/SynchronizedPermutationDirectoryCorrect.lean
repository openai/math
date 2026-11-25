import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectory
import OAI.Computability.NearSquareRoot.SynchronizedPermutationCases
import OAI.Computability.NearSquareRoot.SynchronizedBoxPhysicalLayout
import OAI.Computability.NearSquareRoot.SynchronizedPackedPermutation

/-! # Correctness of the computed per-row permutation directory -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermDirectory

open IntegerMultiplication.Code AxisWord SynchronizedBlocks SynchronizedBorrowing SynchronizedLayers.ScheduleProgram BoxFin

variable {K L : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid K L box)
  [∀ i, NeZero (modulus box i)] (j : Fin (box.length/4))

private def typedRoute (i : Fin (count j)) (b : Fin 15) :=
  ((routingStrides (box := box) j i, RoutingTable.dimensions
    (fiberCount (blockModulus (box := box) j) (blockPadding j) i) (blockModulus j i)
      (blockPadding j i) (2^(expAt box j i)) b), tally (physicalWidth (box := box) j))

include hb in
private theorem seeds_eq (dir : Bool) (i : Fin (count j)) (b : Fin 15) (op : Inst) (micro : Tally) :
    seeds (summary (PermHeader.block box j),PermHeader.fields (PermHeader.block box j,tally i.val),
      dir,(encode (i,b,op),micro)) =
      (directTableQuery j (expAt box j) i b op.1.length op.2.1.length, typedRoute (box := box) j i b) := by
  simp only [seeds,summary, PermHeader.width_eq hb j,PermHeader.volume_eq_pow hb j,PermHeader.low_eq hb j,
    PermHeader.fields_eq hb j i, encode, measures,tally_length, Nat.mod_eq_of_lt b.isLt,
    directTableQuery,packedQuery,typedRoute,RoutingTable.dimensions,routingStrides, unaryPadding, recover_tally]
  rfl

/-- The table scatters to the inverse of the source read by a forward matrix.
Taking the matrix adjoint reverses that convention. -/
def push {A : Type} (dir : Bool) (p : Equiv.Perm A) := bif dir then p else p.symm

private theorem idle_rep (dir : Bool) :
    let e := blockWord hb j
    Benes.RawRepresents (e.symm.trans ((push dir (Equiv.refl _)).trans e))
      (blockEntry (PermHeader.block box j,dir,none)).2 := by
  change Benes.RawRepresents _ (idlePortTable (PermHeader.volume _,PermHeader.width _))
  rw [PermHeader.volume_eq_pow hb j,PermHeader.width_eq hb j]
  cases dir <;> simpa [push] using idlePortTable_represents (physicalWidth (box := box) j)

private theorem live_rep (dir : Bool) (i : Fin (count j)) (b : Fin 15) (op : Inst) (micro : Tally)
    (hc : (micro=[] ∧ (op.1.length=0 ∨ op.1.length=18)) ∨
      (op.1.length=10 ∧ (micro=tally 1 ∨ micro=tally 8))) :
    let z := (encode (i,b,op),micro)
    ∃ p : Equiv.Perm (BlockAddress (BoxAxis box) j),
      boxSlot (physicalLayout hb) j z = .permutation p ∧
        Benes.RawRepresents ((blockWord hb j).symm.trans ((push dir p).trans (blockWord hb j)))
          (blockEntry (PermHeader.block box j,dir,some z)).2 := by
  dsimp only
  let a := axisMod box j
  let c := axisPad box j
  let w := expAt box j
  let har : ∀ i, a i ≤ 2^w i := fun _ => active_bound _
  let hbr : ∀ i, 2*2^w i ≤ 8*a i := fun _ => (doubled_pad_lt (NeZero.pos _)).le
  let he := even_card (numberedBits hb j)
  have D := decode_routes a c w (blockSpectators hb j) har hbr (numberedBits hb j) he (i,b,op)
  let p := (completeMatching a c w (blockSpectators hb j) har hbr he i b).symm.trans (numberedBits hb j).symm
  let g := PermHeader.block box j
  have entry (s : Tally) : (blockEntry (g,dir,some (encode (i,b,op),s))).2 =
      liveTable (summary g,PermHeader.fields (g,tally i.val),dir,(encode (i,b,op),s)) := rfl
  rcases hc with ⟨rfl,ht⟩ | ⟨_,hm⟩
  · let q := opcodeSource a c w (blockSpectators hb j) har hbr i b op.1.length op.2.1.length
    refine ⟨q,decode_opcodeSource a c w (blockSpectators hb j) har hbr (numberedBits hb j) he i b op ht,?_⟩
    rw [entry,liveTable,seeds_eq hb j]
    change Benes.RawRepresents _ (portTable (directTableQuery j w i b op.1.length op.2.1.length))
    have H := directTable_represents hb j w har hbr i b op.1.length op.2.1.length
    have inv : q.symm = q := opcodeSource_inv a c w (blockSpectators hb j) har hbr i b _ _
    cases dir <;> simp only [push,Bool.cond_true,Bool.cond_false,inv] <;> exact H
  · have H := rawRouting_benes hb j w har hbr he i b
    change Benes.RawRepresents _ (RoutingTable.rawRouting (typedRoute (box := box) j i b)).1 ∧
      Benes.RawRepresents _ (RoutingTable.rawRouting (typedRoute (box := box) j i b)).2 at H
    rcases hm with rfl|rfl
    · refine ⟨p,D.1,?_⟩
      rw [entry,liveTable,seeds_eq hb j]
      cases dir
      · exact H.2
      · exact H.1
    · refine ⟨p.symm,D.2,?_⟩
      rw [entry,liveTable,seeds_eq hb j]
      cases dir
      · exact H.1
      · exact H.2

section Emitted

variable {k L : ℕ} (h : BoxShape.Valid k L (CoprimeBox.box k)) [∀ i, NeZero (modulus (CoprimeBox.box k) i)]

/-- Every computed block entry has the physical block width and the exact
scattering graph of the selected local action, including absent fields. -/
theorem directory_represents (dir : Bool) (s : Fin (directedPlan (dir,tally k)).length)
    (b : Fin ((CoprimeBox.box k).length/4))
    (hp : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation) :
    let r := (directedPlan (dir,tally k))[s.val]
    let e := blockWord h b
    ∃ (p : Equiv.Perm (BlockAddress (BoxAxis (CoprimeBox.box k)) b)) (t : Benes.RawTable),
      (readBlock r.2 b.val).elim (.permutation (Equiv.refl _)) (boxSlot (physicalLayout h) b) = .permutation p ∧
      (directory (dir,tally k,tally s.val))[b.val]? = some (tally (physicalWidth (box := CoprimeBox.box k) b),t) ∧
      Benes.RawRepresents (e.symm.trans ((push r.1 p).trans e)) t := by
  let r := (directedPlan (dir,tally k))[s.val]
  let g := PermHeader.block (CoprimeBox.box k) b
  have hperm : r.2.1 = (false,false) := hp
  have hr : r ∈ directedPlan (dir,tally k) := List.getElem_mem _
  have entry := directory_entry dir s b
  cases hz : readBlock r.2 b.val with
  | none =>
    refine ⟨Equiv.refl _,(blockEntry (g,r.1,none)).2,?_,?_,idle_rep h b r.1⟩
    · change (readBlock r.2 b.val).elim _ _ = _
      rw [hz]
      rfl
    · rw [entry]
      change some (fromRow (r,tally b.val,g)) = _
      simp only [fromRow,tally_length,hperm,ite_true,hz]
      exact congrArg (fun w => some (w,(blockEntry (g,r.1,none)).2)) (PermHeader.width_eq h b)
  | some z =>
    obtain ⟨i,j,op,_,z₁,hc⟩ := directed_permutation_cases hr hp b hz
    have zeq : z = (encode (i,j,op),z.2) := Prod.ext z₁ rfl
    obtain ⟨p,hs,ht⟩ := live_rep h b r.1 i j op z.2 hc
    refine ⟨p,(blockEntry (g,r.1,some z)).2,?_,?_,?_⟩
    · change (readBlock r.2 b.val).elim _ _ = _
      rw [hz]
      exact zeq ▸ hs
    · rw [entry]
      change some (fromRow (r,tally b.val,g)) = _
      simp only [fromRow,tally_length,hperm,ite_true,hz]
      exact congrArg (fun w => some (w,(blockEntry (g,r.1,some z)).2)) (PermHeader.width_eq h b)
    · simpa only [← zeq] using ht

include h in
omit [∀ i, NeZero (modulus (CoprimeBox.box k) i)] in
/-- Other stage kinds explicitly emit the identity scattering table in every block. -/
theorem directory_other (dir : Bool) (s : Fin (directedPlan (dir,tally k)).length)
    (b : Fin ((CoprimeBox.box k).length/4))
    (hn : (directedPlan (dir,tally k))[s.val].2.1 ≠ kindCode .permutation) :
    let w := physicalWidth (box := CoprimeBox.box k) b
    (directory (dir,tally k,tally s.val))[b.val]? =
      some (tally w,idlePortTable (tally (2^w),tally w)) := by
  rw [directory_entry]
  have N : (directedPlan (dir,tally k))[s.val].2.1 ≠ (false,false) := hn
  simp only [fromRow,N,ite_false,blockEntry,PermHeader.volume_eq_pow h b,PermHeader.width_eq h b]

end Emitted

end ShortFourier.BatchWord.PermDirectory

end NearSquareRoot
end Computability
end OAI
