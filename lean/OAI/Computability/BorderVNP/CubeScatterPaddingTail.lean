import OAI.Computability.BorderVNP.CubeScatterPaddingLayout
import OAI.Computability.BorderVNP.CubeScatterHostPins
import OAI.Computability.BorderVNP.CubePairDirectory

/-! # The native suffix checks test every physical padding pin

The runtime cursor enumerates all pairs of product labels. Its two owner lookups
recover the two endpoints' group owners. At each owner the resident kind, first
packet, and vertex fields give the same singleton or demand-bit address as the
physical host contraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open HostAddress VPVNP.MotifBase Tally

variable {Team : Type*} {n d blocks b h K s : ℕ}

/-- Three actual directory words used at every product-label pair. -/
def TripleWords (n d blocks table : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ u v : Label (n+1) d,
    let a := table+3*(code u*d^(n+1)+code v)
    mem a = PairDirectory.kind d (code u) (code v) (n+1) ∧
      mem (a+1) = PairDirectory.firstPacketIndex d (code u) (code v) (n+1) blocks ∧
      mem (a+2) = PairDirectory.vertexNo d (code u) (code v) (n+1)

/-- Read the three fields directly from the verified image of the native directory pass. -/
theorem tripleWords_of_image {dir : PairDirectory.Layout} {orig mem : ℕ → ℕ}
    (image : PairDirectory.Image dir orig dir.count mem) (axes : dir.axes = n+1) :
    TripleWords n dir.d dir.blocks dir.table mem := by
  intro u v
  have z : dir.Z = dir.d^(n+1) := by simp [PairDirectory.Layout.Z,axes]
  have lt (x : Label (n+1) dir.d) : code x < dir.Z := z ▸ (finFunctionFinEquiv x).isLt
  simpa only [z,axes] using image.lookup (code u) (code v) (lt u) (lt v)

/-- Identification of a team's actual padding cache and memory tables with the
physical grouping, banks and occupied-width array. -/
structure TailHeader (i : Fin (n+1)) (group : Fin d → Team) (number : Team ↪ ℕ)
    (t : Team) (l : Layout) (mem used : ℕ → ℕ) (blocks b h K s : ℕ) : Prop where
  /-- Product alphabet size, radix, and selected coordinate place. -/
  alphabet : l.labels = d^(n+1) ∧ l.groups = d ∧ l.place = d^i.val
  /-- Native bin and packet bank shape. -/
  banks : l.blocks = blocks ∧ l.bc = h*b ∧ l.bankWidth = bankWidth n b h K s ∧
    l.selectorWidth = selectorWidth n K h
  /-- The physical site number stored in the public cache. -/
  site : l.team = number t
  /-- The owner table stores the physical team for every symbol of this coordinate. -/
  owners : ∀ g : Fin d, mem (l.owners+g.val) = number (group g)
  /-- The occupied-width words are those of the actual directed interval table. -/
  widths : ∀ key < l.count, mem (l.widths+key) = used key
  /-- Kind, first packet and vertex read from the actual native pair directory. -/
  triples : TripleWords n d blocks l.triples mem

private theorem key_lt (u v : Label (n+1) d) :
    code u*d^(n+1)+code v < d^(n+1)*d^(n+1) := by
  have hu := Nat.mul_le_mul_right (d^(n+1)) (finFunctionFinEquiv u).isLt
  rw [Nat.succ_mul] at hu
  exact (Nat.add_lt_add_left (finFunctionFinEquiv v).isLt _).trans_le hu

private theorem key_parts (u v : Label (n+1) d) :
    (code u*d^(n+1)+code v)/d^(n+1) = code u ∧ (code u*d^(n+1)+code v)%d^(n+1) = code v := by
  have hv : code v < d^(n+1) := (finFunctionFinEquiv v).isLt
  rw [Nat.mul_comm (code u),Nat.mul_add_div (Nat.zero_lt_of_lt hv),Nat.div_eq_of_lt hv,
    Nat.add_zero,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hv]
  exact ⟨rfl,rfl⟩

private theorem key_surj {k : ℕ} (hk : k < d^(n+1)*d^(n+1)) :
    ∃ u v : Label (n+1) d, code u*d^(n+1)+code v = k := by
  have pos : 0 < d^(n+1) := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp [this] at hk
  let u : Fin (d^(n+1)) := ⟨k/d^(n+1),(Nat.div_lt_iff_lt_mul pos).2 hk⟩
  let v : Fin (d^(n+1)) := ⟨k%d^(n+1),Nat.mod_lt _ pos⟩
  refine ⟨finFunctionFinEquiv.symm u,finFunctionFinEquiv.symm v,?_⟩
  simp only [code,Equiv.apply_symm_apply,u,v]
  exact Nat.div_add_mod' ..

private theorem kind_cases (d u v axes : ℕ) :
    PairDirectory.kind d u v axes = 0 ∨ PairDirectory.kind d u v axes = 1 := by
  induction axes with
  | zero => exact Or.inr rfl
  | succ a ih => rw [PairDirectory.kind]; split <;> simp_all

variable {i : Fin (n+1)} {group : Fin d → Team} {number : Team ↪ ℕ}
  {t : Team} {l : Layout} {mem used : ℕ → ℕ}

/-- The integer digit read in register 33 belongs to the same owner as the native
endpoint of the original label pair. -/
theorem TailHeader.owner_eq (header : TailHeader i group number t l mem used blocks b h K s)
    (u v : Label (n+1) d) (side : Bool) :
    l.owner mem (code u*d^(n+1)+code v) side = number (endOwner i group side (u,v)) := by
  obtain ⟨hd,hg,hp⟩ := header.alphabet
  obtain ⟨hu,hv⟩ := key_parts u v
  cases side <;> simp only [Layout.owner,Layout.ownerAt,Layout.label,endOwner,Bool.false_eq_true,
    ↓reduceIte,hd,hg,hp,hu,hv]
  · exact (congrArg (fun k => mem (l.owners+k)) (code_digit u i)).trans (header.owners (u i))
  · exact (congrArg (fun k => mem (l.owners+k)) (code_digit v i)).trans (header.owners (v i))

/-- At the computed suffix index, the native cache reads the same bit address as the
singleton or antipodal packet of the physical host. -/
theorem TailHeader.source_eq (header : TailHeader i group number t l mem used blocks b h K s)
    (u v : Label (n+1) d) (side : Bool) (j : ℕ) :
    (l.fields mem (code u*d^(n+1)+code v) side).source j =
      address d (n+1) blocks (h*b) l.packets (bankWidth n b h K s) (selectorWidth n K h)
        l.singles (code u) (code v) (used (code u*d^(n+1)+code v)+j) side := by
  obtain ⟨hk,hf,hv⟩ := header.triples u v
  have lt := key_lt u v
  have hw := header.widths _ (show _ < l.count by simpa [Layout.count,header.alphabet.1] using lt)
  obtain ⟨hb,hbc,hbw,hs⟩ := header.banks
  rcases kind_cases d (code u) (code v) (n+1) with kind | kind <;>
    simp [Layout.fields,HostScatter.BitFields.source,address,hw,hk,hf,hv,hb,hbc,hbw,hs,kind]
  simp only [Nat.add_assoc]

/-- Across every actual team, passing the numeric directory scans is equivalent to
checking both owners of every unoccupied ordinal in the original product-label bins. -/
theorem valid_iff_tailTests {layout : Team → Layout} {memory : Team → ℕ → ℕ}
    (headers : ∀ t, TailHeader i group number t (layout t) (memory t) used blocks b h K s) :
    (∀ t, (layout t).Valid (memory t)) ↔ TailTests i group (fun t => (layout t).packets)
      (fun t => (layout t).singles) K s h b blocks memory used := by
  have width (t : Team) (k : ℕ) (hk : k < (layout t).count) (side : Bool) :
      ((layout t).fields (memory t) k side).width = blocks*(h*b)-used k := by
    simp [Layout.fields,Layout.stride,(headers t).banks.1,(headers t).banks.2.1,(headers t).widths k hk]
  constructor
  · intro tests t u v side own j hj
    let k := code u*d^(n+1)+code v
    change used k ≤ j.val at hj
    have hk : k < (layout t).count := by simpa [k,Layout.count,(headers t).alphabet.1] using key_lt u v
    have owner := ((headers t).owner_eq u v side).trans ((congrArg number own).trans (headers t).site.symm)
    have run := tests t k hk side owner (j.val-used k) (by rw [width t k hk side]; have := j.isLt; omega)
    rw [(headers t).source_eq u v side] at run
    simpa only [← show k = code u*d^(n+1)+code v from rfl,Nat.add_sub_of_le hj] using run
  · intro tests t k hk side owner j hj
    have bound : k < d^(n+1)*d^(n+1) := by simpa [Layout.count,(headers t).alphabet.1] using hk
    obtain ⟨u,v,rfl⟩ := key_surj bound
    rw [(headers t).source_eq u v side]
    refine tests t u v side ?_ ⟨_,?_⟩ ?_
    · apply number.injective
      exact ((headers t).owner_eq u v side).symm.trans (owner.trans (headers t).site)
    · rw [width _ _ hk side] at hj
      omega
    · exact Nat.le_add_right ..

open Crossing Physical NativeIntervals

/-- With the true directed interval image and scattered endpoint banks, the native
checks are precisely both zero pins outside the embedded live cable intervals. -/
theorem valid_iff_pins {D m : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
    {N : Network D P bits} {cell : N.Site → Cell} {interval : NativeIntervals.Layout}
    {before dir : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin m ↪o Fin interval.count}
    {cells : Cell ↪ ℕ} {label : Cell → Label (n+1) d} {hz : d^(n+1) = interval.alphabet}
    (rows : PhysicalRows N cell interval before ord row cells label (productCode n d interval.alphabet hz))
    (image : interval.Image before interval.count dir) (cap)
    {layout : Team → Padding.Layout} {memory : Team → ℕ → ℕ}
    {single : SingleSlot n d blocks (h*b) → Bool} {ends : Packet n d blocks → Ends n → Fin (h*b) → Bool}
    (banks : EndBanks i group (fun t => (layout t).packets) (fun t => (layout t).singles) memory single ends K s)
    (headers : ∀ t, TailHeader i group number t (layout t) (memory t)
      (fun k => dir (interval.widths+k)) blocks b h K s) :
    (∀ t, (layout t).Valid (memory t)) ↔
      ∀ q ∉ Set.range (packedSlotEmbedding N cell ord label blocks (h*b) cap),
        readEnd single ends false q = false ∧ readEnd single ends true q = false :=
  (valid_iff_tailTests headers).trans (tailTests_iff rows image cap banks)

end Cube.Padding

end BorderVNP
end Computability
end OAI
