import OAI.Computability.BorderVNP.DiagonalTallyRAMAllocate

/-! # The complete tally instruction path with its runtime allocator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyScatter
open DiagonalTallyMaterialize (Operand digitRefsAt supplied)

/-- Allocate from the delivered count, generate the records, clear the scratch bank,
verify the team's row and serialize the sums of the entire common table. -/
def allocateAndEvaluate : Code := .seq allocateTallies evaluateTallies

/-- Exact read footprint of the delivered sparse operand descriptors. -/
def operandReads (p : ℕ) (os : List Operand) (q : ℕ) : Prop :=
  match os with
  | [] => False
  | o::tail => (p≤q ∧ q<p+5) ∨ q=o.offsetAddr ∨ q=o.placeAddr ∨
    (o.digitsAddr≤q ∧ q<o.digitsAddr+o.digits.length) ∨ (∃ r∈o.digits,r.1=q) ∨ operandReads (p+5) tail q

/-- These are precisely the physical words updated by the allocator. -/
def outsidePointers (d q : ℕ) : Prop := q≠d+32 ∧ q≠d+37 ∧ q≠d+41 ∧ q≠d+42 ∧ q≠d+43

variable {w : ℕ}

private theorem refs_unchanged (m m' : Memory w) (p : ℕ) (ds : List (ℕ × Bool))
    (h : digitRefsAt m p ds) (he : ∀ q, (p≤q ∧ q<p+ds.length) ∨ (∃ r∈ds,r.1=q) → m' q=m q) :
    digitRefsAt m' p ds := by
  induction ds generalizing p with
  | nil => trivial
  | cons d ds ih =>
    obtain ⟨q,b⟩ := d
    refine ⟨(congrArg Fin.val (he p (.inl ⟨le_rfl,by simp⟩))).trans h.1,
      (congrArg Fin.val (he q (.inr ⟨(q,b),List.mem_cons_self,rfl⟩))).trans h.2.1,
      ih _ h.2.2 ?_⟩
    intro i hi
    rcases hi with hi | ⟨r,hr,rr⟩
    · apply he _ (.inl ⟨by omega,?_⟩); simp; omega
    · exact he _ (.inr ⟨r,.tail _ hr,rr⟩)

private theorem supplied_unchanged (m m' : Memory w) (p limit : ℕ) (os : List Operand)
    (hs : supplied m limit p os) (he : ∀ q, operandReads p os q → m' q=m q) :
    supplied m' limit p os := by
  induction os generalizing p with
  | nil => trivial
  | cons o os ih =>
    obtain ⟨hptr,before,⟨a,b,c,d,e,f,g,r⟩,fit,tail⟩ := hs
    have hq (j : ℕ) (hj : j<5) : (m' (p+j)).val=(m (p+j)).val :=
      congrArg Fin.val (he _ (.inl ⟨by omega,by omega⟩))
    have hOff := congrArg Fin.val (he _ (.inr (.inl rfl)))
    have hPlace := congrArg Fin.val (he _ (.inr (.inr (.inl rfl))))
    refine ⟨hptr,before,⟨?_,(hq 1 (by decide)).trans b,hOff.trans c,
      (hq 2 (by decide)).trans d,(hq 3 (by decide)).trans e,(hq 4 (by decide)).trans f,hPlace.trans g,
      refs_unchanged m m' o.digitsAddr o.digits r ?_⟩,fit,ih (p+5) tail ?_⟩
    · simpa using (hq 0 (by decide)).trans a
    · intro q h
      apply he _ (.inr (.inr (.inr ?_)))
      exact h.elim Or.inl (fun z => .inr (.inl z))
    · intro q h
      exact he _ (.inr (.inr (.inr (.inr (.inr h)))))

/-- Recover the full source-frame condition from the original memory after the allocator
writes its five pointer slots. The operand and raw-broadcast conditions require only the
physical words actually reached by the later probes. -/
theorem Arena.source_after_allocation (a : Arena) (pub : Arg → Word w) (m mt : Memory w)
    (os : List Operand) (xs : List (List Bool)) (p : ℕ) (fit : a.Fits w (pub 0).val)
    (image : readings mt=a.installed w (pub 0).val (readings m))
    (dir : a.frame.resident pub mt) (outFrame : serializeFrame pub mt (a.bitFrame w) a.dim)
    (ptr : (mt ((pub 0).val+44)).val=p) (ops : supplied m a.fresh p os)
    (opSep : ∀ q, operandReads p os q → outsidePointers (pub 0).val q)
    (rawSep : ∀ q, a.raw≤q → q<a.raw+(a.teams*a.dim)*a.width → outsidePointers (pub 0).val q)
    (count : os.length=a.count) (coords : ∀ o∈os,o.pair.1<a.dim)
    (sums : ∀ c<a.dim,a.localRow os c<2^w)
    (raw : DiagonalTallyBits.WordsAt m a.raw xs) (num : xs.length=a.teams*a.dim)
    (lengths : ∀ b∈xs,b.length=a.width) :
    a.Source pub mt os xs p := by
  have keep (q : ℕ) (h : outsidePointers (pub 0).val q) : mt q=m q := by
    apply Fin.ext
    change readings mt q = readings m q
    rw [image,a.installed_outside _ _ _ _ h]
  refine ⟨fit,dir,outFrame,ptr,supplied_unchanged m mt p a.fresh os ops (fun q hq => keep q (opSep q hq)),
    count,coords,sums,?_,num,lengths⟩
  apply DiagonalTallyBits.words_congr m mt a.raw a.width xs raw lengths
  intro q hq hi
  rw [num] at hi
  exact keep q (rawSep q hq hi)

/-- A single fixed instruction table computes the natural global sums directly from
the actual pre-allocation state and the canonical common bit prefix. -/
theorem allocateAndEvaluate_natural_runs (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (p : ℕ) (rows : Fin a.teams → Fin a.dim → ℕ)
    (seed : a.seed pub m p) (fit : a.Fits w (pub 0).val) (hdir : (pub 0).val+101 < 2^w)
    (ops : supplied m a.fresh p os) (opSep : ∀ q, operandReads p os q → outsidePointers (pub 0).val q)
    (rawSep : ∀ q, a.raw≤q → q<a.raw+(a.teams*a.dim)*a.width → outsidePointers (pub 0).val q)
    (count : os.length=a.count) (coords : ∀ o∈os,o.pair.1<a.dim)
    (bits : DiagonalTallyBits.WordsAt m a.raw (broadcast a.width rows))
    (localCounts : ∀ c, a.localRow os c.val=rows ⟨a.team,fit.team⟩ c)
    (rowFit : ∀ i c,rows i c<2^a.width) (sumFit : ∀ c, ∑ i, rows i c<2^w) :
    ∃ es t m', Runs pub mac allocateAndEvaluate s m es t m' ∧
      traceCost es ≤ allocateTallies.slots+a.work w os ∧
      (∀ e∈es,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin a.dim, ∀ j<w, m' ((a.bitFrame w).dst+(c.val*w+j)) =
        word w (((∑ i,rows i c).testBit j).toNat) := by
  obtain ⟨x,t,mt,rx,hx,image,dir,output,ptr⟩ := allocateTallies_runs a pub mac s m p seed fit hdir
  have source := a.source_after_allocation pub m mt os (broadcast a.width rows) p fit image dir output ptr
    ops opSep rawSep count coords (fun j hj => by
      have he := localCounts ⟨j,hj⟩
      exact he ▸ (rowFit ⟨a.team,fit.team⟩ ⟨j,hj⟩).trans_le (Nat.pow_le_pow_right (by decide) fit.width))
    bits (by simp [broadcast]) (by
      intro b hb
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      exact length_wordBits _)
  obtain ⟨y,u,mu,ry,hy,_,out⟩ := evaluateTallies_natural_runs a pub mac t mt os p rows source rowFit localCounts sumFit
  have run := rx.seq ry
  refine ⟨_,u,mu,run,?_,ordinary_run (show ordinary allocateAndEvaluate = true by decide) run,out⟩
  rw [show traceCost (x++y)=traceCost x+traceCost y from VPVNP.RAMBuckets.cost_append ..]
  exact Nat.add_le_add hx hy

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
