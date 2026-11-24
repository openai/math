import OAI.Computability.VPVNP.CompressorRecordsBundleWidthScatter
import OAI.Computability.VPVNP.CompressorRecordsBundleRoleIndex

/-!
# Absolute role-table identifiers in dense CD piece order

A source port gives its residual lane by division by the old degree and
reduction modulo the lane radix. Append this lane to its normalized CD key
and scatter the resulting word by classified owner and sorted rank. The
preceding rectangle receives the thick wires' auxiliary words. The CD
rectangle has one entry for every motif and no holes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.MotifAbsolute

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.PackingData
open BundleLists BundleKeys BundleWidthScatter

variable {w : ℕ}

/-- The first five parameters use the shared scatter layout. The last two
are the old degree and the residual-lane radix. -/
def columns (p : Fin 7 → Word w) : Fin 5 → Word w := fun t ↦ p (t.castAdd 2)

/-- Encode an old port's absolute identifier by appending its residual-lane digit to the
normalized key, using the old degree and lane radix. -/
def payload (p : Fin 7 → Word w) (i key : Word w) : Word w :=
  key*p 6 + BinaryOp.mod.eval (BinaryOp.div.eval i (p 5)) (p 6)

/-- Native scatter visit that reads an old port's owner, sorted rank and key, writes its
lane-extended key at the owner and rank, and advances the cursor. -/
def visit : List (Op 7 7) :=
  [.stateWord 0, .publicWord 1 0, .binary .add 1 1 0, .read 2 1,
   .publicWord 1 1, .binary .add 1 1 0, .read 3 1,
   .publicWord 1 2, .binary .add 1 1 0, .read 4 1,
   .publicWord 1 3, .binary .mul 2 2 1, .publicWord 1 4, .binary .add 2 1 2,
   .binary .add 2 2 3, .publicWord 5 5, .binary .div 5 0 5, .publicWord 6 6,
   .binary .mod 5 5 6, .binary .mul 4 4 6, .binary .add 4 4 5,
   .write 2 4, .constant 1 1, .binary .add 0 0 1]

/-- Chronological trace for one absolute-identifier scatter, with the three observed source
words, the write to the classified row, and the intervening ticks. -/
def events (p : Fin 7 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let q := columns p
  let read (t : Fin 3) := Event.read (source q t i) (m (source q t i).val)
  [.tick,.tick,.tick,read 0,.tick,.tick,read 1,.tick,.tick,read 2,
   .tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,
   .write (outAddress q m i) (payload p i (width q m i)),.tick,.tick]

theorem native (p : Fin 7 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 25 (M.program.start i) m [] = some ⟨events p m i,some (i+1)⟩ := by
  change execute ((template visit 0).instantiate w p).program (1+visit.length)
    ⟨_,i,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  rfl

theorem run (p : Fin 7 → Word w) (initial : Memory w) (A : ℕ) (reg : Regions (columns p) initial A) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 25 (some 0) initial (List.replicate A []) = some rs ∧
      endState (some 0) rs = some (word A) ∧ Filled (columns p) initial (after initial (eventLog rs)) A (payload p) ∧
      rs.length = A ∧ (∀ r ∈ rs, r.events.length = 24 ∧ r.probes = 4) ∧ RAMBuckets.cost Report.probes rs = 5*A := by
  apply scatter_values _ _ _ (columns p) initial A reg (payload p)
  exact fun m i ↦ ⟨events p m i,native p m i,rfl,rfl,rfl⟩

variable {V H Tag L : Type} {d c n : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]

/-- All dense addresses are used once. Recovering a motif from a dense index
recovers both its absolute bundle and its sorted piece number. -/
def denseIndex (P : PackingData V H Tag L d c) (site : Site V Tag L ≃ Fin n) (cd : P.BundleNumbering) :
    P.Motif ≃ Fin ((n*d)*pieceCount d c) :=
  ((Equiv.sigmaFiberEquiv P.bundle).symm.trans (Equiv.sigmaEquivProdOfEquiv cd)).trans
    (((portIndex site).prodCongr (Equiv.refl _)).trans finProdFinEquiv)

theorem denseIndex_val (P : PackingData V H Tag L d c) (site : Site V Tag L ≃ Fin n)
    (cd : P.BundleNumbering) (b : Port V Tag L d) (x : P.MotifFiber b) :
    (denseIndex P site cd x.1).val = (portIndex site b).val*pieceCount d c + (cd b x).val := by
  rcases x with ⟨x,hx⟩
  subst b
  change _ + _ * _ = _ * _ + _
  ac_rfl

variable {a g N : ℕ} (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g))) (order : V ≃ Fin N)

local notation "P" => orderedDyadicPacking G order
local notation "D" => 2^a
local notation "C" => Shrink.colors a
local notation "J" => Shrink.J a
local notation "A" => (N*2^(packingLaneBits a g))*D
local notation "B" => numBundles N a g
local notation "Q" => pieceCount D C
local notation "arcs" => oldArcOrder (a := a) (g := g) order
local notation "sites" => Shrink.packedIndex (a := a) (g := g) order

/-- The compact role-table identifier in the exact order of the slot compiler. -/
abbrev absoluteIndex := Slots.oldArcIndex P order (bitWordFinEquiv J) (bitWordFinEquiv g)

private theorem lane_value (e : OldArc V a g) :
    (arcs e).val / D % 2^g = (bitWordFinEquiv g e.1.1.2.2).val := by
  rw [oldArcOrder_val, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt e.1.2.isLt, Nat.add_zero]
  let high := Shrink.join a (Shrink.join C (order e.1.1.1).val (bitWordFinEquiv C e.2.1).val)
    (bitWordFinEquiv a e.2.2).val
  let tag := (bitWordFinEquiv J e.1.1.2.1).val
  let lane := (bitWordFinEquiv g e.1.1.2.2).val
  change (high*2^(J+g) + (tag*2^g+lane)) % 2^g = lane
  rw [pow_add, show high*(2^J*2^g)+(tag*2^g+lane) = (high*2^J+tag)*2^g+lane by ring,
    Nat.mul_add_mod_of_lt (Fin.isLt _)]

theorem payload_motif (p : Fin 7 → Word w) (hd : (p 5).val = D) (hl : (p 6).val = 2^g)
    (ha : A ≤ 2^w) (e : (P).Motif) :
    payload p (arcWord arcs e.1) (word (keyAt order false e.1)) = word ((absoluteIndex G order e.1).val) := by
  let i := arcWord (w := w) arcs e.1
  have hi : i.val = (arcs e.1).val := Nat.mod_eq_of_lt ((arcs e.1).isLt.trans_le ha)
  have divVal : (BinaryOp.div.eval i (p 5)).val = i.val/(p 5).val := Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt i.isLt)
  have hmod : BinaryOp.mod.eval (BinaryOp.div.eval i (p 5)) (p 6) =
      word (bitWordFinEquiv g e.1.1.1.2.2).val := by
    change Fin.ofNat _ ((BinaryOp.div.eval i (p 5)).val % (p 6).val) = _
    rw [divVal,hi,hd,hl,lane_value order e.1]
  have hr : p 6 = word (2^g) := Fin.ext (by rw [← hl]; exact (Nat.mod_eq_of_lt (p 6).isLt).symm)
  change word _ * p 6 + BinaryOp.mod.eval (BinaryOp.div.eval i (p 5)) (p 6) = _
  rw [hmod,hr]
  change _ = word (Slots.oldArcIndex P order (bitWordFinEquiv J) (bitWordFinEquiv g) e.1).val
  rw [oldArcIndex_eq_key_lane G order]
  apply Fin.ext
  simp [word, Fin.val_add, Fin.val_mul, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod]

/-- Read all three columns at the physical port. The normalized key is needed
only on a CD port. Thick scratch words may have arbitrary values. -/
structure Inputs (p : Fin 7 → Word w) (initial : Memory w) (cd : (P).BundleNumbering) (dd : (P).ThickNumbering) : Prop where
  owners : ∀ e, initial (source (columns p) 0 (arcWord arcs e)).val = word (bucketIndex sites (bucketOf P e)).val
  ranks : ∀ e, initial (source (columns p) 1 (arcWord arcs e)).val = word (rankOf P cd dd e)
  keys : ∀ e : (P).Motif, initial (source (columns p) 2 (arcWord arcs e.1)).val = word (keyAt order false e.1)

/-- The owner and rank cells coincide with the previously constructed width
scatter inputs. Only the third column is changed to the classifier's key. -/
theorem Inputs.of_ranked {p : Fin 7 → Word w} {initial : Memory w}
    {cd : (P).BundleNumbering} {dd : (P).ThickNumbering}
    {s : Fin 5 → Word w} {old : OldArc V a g → ℕ} (h : RankedInput P cd dd arcs sites s initial old)
    (ownerBase : (columns p) 0 = s 0) (rankBase : (columns p) 1 = s 1)
    (fit : (p 2).val + A ≤ 2^w)
    (keys : ∀ x : (P).Motif, initial ((p 2).val+(arcs x.val).val) = word (keyAt order false x.val)) :
    Inputs G order p initial cd dd := by
  refine ⟨fun e ↦ ?_,fun e ↦ ?_,fun x ↦ ?_⟩
  · change initial ((columns p) 0 + arcWord arcs e).val = _
    rw [ownerBase]; exact h.owners e
  · change initial ((columns p) 1 + arcWord arcs e).val = _
    rw [rankBase]; exact h.ranks e
  · change initial (p 2 + arcWord arcs x.val).val = _
    rw [Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by have := (arcs x.val).isLt; omega)]
    exact keys x

/-- Contents of every dense cell, including the complete inverse enumeration. -/
def Directory (cd : (P).BundleNumbering) (denseBase : Word w) (final : Memory w) : Prop :=
  ∀ i, (final (denseBase.val+i.val)).val =
    (absoluteIndex G order ((denseIndex P sites cd).symm i).1).val

theorem Directory.atPiece {cd : (P).BundleNumbering} {denseBase : Word w} {final : Memory w}
    (h : Directory G order cd denseBase final) (b : Port V (BitWord J) (BitWord g) D) (j : Fin Q) :
    (final (denseBase.val + ((portIndex sites b).val*Q + j.val))).val =
      (absoluteIndex G order ((cd b).symm j).1.1).val := by
  let x := (cd b).symm j
  have hv := denseIndex_val P sites cd b x
  rw [show cd b x = j from (cd b).apply_symm_apply j] at hv
  simpa only [Equiv.symm_apply_apply, hv] using h (denseIndex P sites cd x.1)

/-- A single physical scan emits every requested absolute motif identifier
into its dense rank cell. Its frame preserves every address outside occupied
CD and thick scratch cells. -/
theorem graph_run (p : Fin 7 → Word w) (initial : Memory w) (cd : (P).BundleNumbering) (dd : (P).ThickNumbering)
    (denseBase : Word w) (layout : BundleWidthScatter.Layout (columns p) A (N*(2^J*2^g)) D C)
    (hd : (p 5).val = D) (hl : (p 6).val = 2^g) (stride : ((columns p) 3).val = Q)
    (dense : denseBase.val = ((columns p) 4).val + B*Q) (read : Inputs G order p initial cd dd) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 25 (some 0) initial (List.replicate A []) = some rs ∧
      endState (some 0) rs = some (word A) ∧ Filled (columns p) initial (after initial (eventLog rs)) A (payload p) ∧
      rs.length = A ∧ (∀ r ∈ rs, r.events.length = 24 ∧ r.probes = 4) ∧ RAMBuckets.cost Report.probes rs = 5*A ∧
      Directory G order cd denseBase (after initial (eventLog rs)) := by
  let q := columns p
  let old := fun e ↦ (width q initial (arcWord arcs e)).val
  have hcols : RankedInput P cd dd arcs sites q initial old := ⟨read.owners,read.ranks,fun _ ↦ rfl⟩
  have ha : A ≤ 2^w := by have := layout.sourceFits 0; omega
  have hcard := Fintype.card_congr ((arcs).symm.trans (absoluteIndex G order))
  simp only [Fintype.card_fin] at hcard
  obtain ⟨rs,hr,he,hf,hln,hw,hc⟩ := run p initial A (regions_of_layout P cd dd arcs sites layout hcols)
  refine ⟨rs,hr,he,hf,hln,hw,hc,fun i ↦ ?_⟩
  let m := (denseIndex P sites cd).symm i
  let b := (P).bundle m
  let x : (P).MotifFiber b := ⟨m,rfl⟩
  have hx : (denseIndex P sites cd x.1).val = i.val := congrArg Fin.val ((denseIndex P sites cd).apply_symm_apply i)
  have hdense := (denseIndex_val P sites cd b x).symm.trans hx
  have dest := output_eq P cd dd arcs sites layout hcols x.1.1
  change (outAddress q initial (arcWord arcs x.1.1)).val = (q 4).val +
    ((bucketIndex sites (bucketOf P x.1.1)).val*(q 3).val + rankOf P cd dd x.1.1) at dest
  rw [bucketOf_motif P x.1, rank_motif P cd dd x, show (bucketIndex sites (.inr ((P).bundle x.1))).val = B+
    (portIndex sites b).val from rfl, stride, Nat.add_mul, Nat.add_assoc, hdense, ← Nat.add_assoc, ← dense] at dest
  have hs := hf.readback (arcs x.1.1).val (arcs x.1.1).isLt
  change after initial (eventLog rs) (outAddress q initial (arcWord arcs x.1.1)).val =
    payload p (arcWord arcs x.1.1) (initial (source q 2 (arcWord arcs x.1.1)).val) at hs
  rw [dest, read.keys x.1, payload_motif G order p hd hl ha x.1] at hs
  have fit := (absoluteIndex G order x.1.1).isLt.trans_le (hcard ▸ ha)
  exact (congrArg Fin.val hs).trans (Nat.mod_eq_of_lt fit)

end CompressorRecords.MotifAbsolute

end VPVNP
end Computability
end OAI
