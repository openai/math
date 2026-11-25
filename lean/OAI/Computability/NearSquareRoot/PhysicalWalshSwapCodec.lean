import OAI.Computability.NearSquareRoot.PhysicalWalshPadding
import OAI.Computability.IntegerMultiplication.Carry.Shrink
import OAI.Computability.IntegerMultiplication.Loom.Skein

/-! # Fixed-width Walsh records on a binary interchange tape

The real and imaginary words are consecutive in each bitstring. They occupy
identical widths, so their boundary can be recovered by halving the length of
the stored bitstring. Both conversions run in linear time and space.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshSwapCodec

open IntegerMultiplication Code Strip Loom Space

def encode (p : Dusk.Pair) : List Bool := p.1 ++ p.2

def decode (bits : List Bool) : Dusk.Pair := cutLists ((Carry.half (ruler bits)).1,bits)

@[fun_prop] theorem encode_easy : Easy encode := by unfold encode; fun_prop

@[fun_prop] theorem decode_easy : Easy decode :=
  easy_cut (((Easy.identity.ruler.compose Carry.halfCost).compose Easy.fst).pair Easy.identity)

def word {w : ℕ} (x : Dusk.Grain w) := encode (Dusk.mark x)

@[simp] theorem word_length {w : ℕ} (x : Dusk.Grain w) : (word x).length = 2*(w+1) := by
  simp [word,encode,Dusk.mark,Nat.two_mul]

@[simp] theorem decode_word {w : ℕ} (x : Dusk.Grain w) : decode (word x) = Dusk.mark x := by
  simp only [decode,Carry.half_v,ruler_length,word_length,Nat.mul_div_cancel_left _ (by decide : 0<2)]
  exact Piecework.cut_of_length _ _ _ (by simp [Dusk.mark])

/-- The bead at each position has the same physical leaf as the corresponding bit. -/
noncomputable def bitstringBeads {m : ℕ} (bits : List Bool) (h : bits.length=m) : Fin m → Bead :=
  fun j => notify.symm (bits[j.val]'(h ▸ j.isLt))

theorem strip_bitstring {m : ℕ} (bits : List Bool) (h : bits.length=m) :
    strip (Series.natural m) (bitstringBeads bits h) = send bits := by
  let bs (i : Fin m) := bits[i.val]'(h ▸ i.isLt)
  have repr (i : Fin m) : send (bitstringBeads bits h i) = send (bs i) := by
    change Tree.atom (notify (notify.symm _)) = Tree.atom _
    rw [Equiv.apply_symm_apply]
  unfold strip
  simp_rw [repr]
  rw [stripe_eq']
  congr 1
  apply List.ext_getElem (by simp [h])
  intro i hi hj
  simp [Series.natural,Series.fixed,Series.tab,bs]

noncomputable def beads {w : ℕ} (x : Dusk.Grain w) : Fin (2*(w+1)) → Bead :=
  bitstringBeads (word x) (word_length x)

@[simp] theorem strip_beads {w : ℕ} (x : Dusk.Grain w) :
    strip (Series.natural (2*(w+1))) (beads x) = send (word x) :=
  strip_bitstring _ _

theorem strip_table {w : ℕ} {A : Type} (s : Series A) (x : A → Dusk.Grain w) :
    stripe s (fun a => strip (Series.natural (2*(w+1))) (beads (x a))) =
      send ((s.tab x).map word) := by
  simp_rw [strip_beads]
  rw [stripe_eq',Series.map_tab]
  rfl

theorem words_size {w : ℕ} (xs : List (Dusk.Grain w)) :
    size (xs.map word) = xs.length*(4*(w+1)+2)+1 := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,size_cons, Bits.size_word,word_length,ih,
      List.length_cons,Nat.succ_mul]; omega

variable {I : Type} (w : I → ℕ) (x : (i : I) → List (Dusk.Grain (w i)))

theorem encodeRows :
    let V i := ((x i).length+1)*(w i+1)
    BoundedTask V V (fun i => send ((x i).map Dusk.mark)) (fun i => send ((x i).map word)) := by
  intro V
  have run := encode_easy.mapping.on (fun i => (x i).map Dusk.mark)
  simp only [List.map_map] at run
  apply (BoundedTask.of_time run).bound 12 24 <;> intro i
  · rw [PhysicalWalsh.Padding.marks_size]; dsimp [V]; ring_nf; omega
  · change size ((x i).map Dusk.mark)+size ((x i).map Dusk.mark)+1 ≤ 24*(V i+1)
    rw [PhysicalWalsh.Padding.marks_size]; dsimp [V]; ring_nf; omega

theorem decodeRows :
    let V i := ((x i).length+1)*(w i+1)
    BoundedTask V V (fun i => send ((x i).map word)) (fun i => send ((x i).map Dusk.mark)) := by
  intro V
  have run := decode_easy.mapping.on (fun i => (x i).map word)
  simp only [List.map_map, Function.comp_def, decode_word] at run
  apply (BoundedTask.of_time run).bound 12 24 <;> intro i
  · rw [words_size]; dsimp [V]; ring_nf; omega
  · change size ((x i).map word)+size ((x i).map word)+1 ≤ 24*(V i+1)
    rw [words_size]; dsimp [V]; ring_nf; omega

private def reshapeBy (u : List Tally × List (List Bool)) :=
  (Piecework.segment u.1 u.2.flatten).1

private theorem reshapeBy_easy : Easy reshapeBy :=
  ((Easy.fst.pair (Easy.snd.compose Easy.flatten)).compose Piecework.easy).compose Easy.fst

private theorem send_count {X : Type} [Codec X] (x : X) : (send x).count = size x := rfl

private theorem cutSizes (n b : ℕ) :
    size (List.replicate n (tally b)) = n*(2*b+2)+1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ,size_cons,ih,size_tally,tally_length]
    ring

/-- A single streaming repartition of arbitrary incoming bitstrings. The
machine expands the two tallies to the exact cut list, then cuts the bit
transcript into equal-width rows. Neither row count nor row width is fixed
in the program. -/
theorem reshape (rows width : I → ℕ) (xs ys : I → List (List Bool))
    (same : ∀ i, (xs i).flatten = (ys i).flatten)
    (count : ∀ i, (ys i).length = rows i)
    (lengths : ∀ i y, y ∈ ys i → y.length = width i) :
    let V i := size (xs i)+(rows i+1)*(width i+1)
    BoundedTask V V (fun i => send ((tally (rows i),tally (width i)),xs i))
      (fun i => send (ys i)) := by
  intro V
  let cuts i := List.replicate (rows i) (tally (width i))
  let hdr i := (tally (rows i),tally (width i))
  have gen := (generate.on hdr).left (fun i => send (xs i))
  have split := reshapeBy_easy.on (fun i => (cuts i,xs i))
  have ok i : reshapeBy (cuts i,xs i) = ys i := by
    change (Piecework.segment (List.replicate _ _) (xs i).flatten).1 = _
    rw [same,← many (ys i) _ _ (count i) (lengths i), Piecework.prescribed]
  simp only [ok] at split
  have g : Task (fun i => (rows i+1)*size (tally (width i)))
      (fun i => send (hdr i,xs i)) (fun i => send (cuts i,xs i)) := by
    simpa only [hdr,cuts,tally_length,Nat.add_comm,send_prod,size] using gen
  have run := g.compose split
  apply (BoundedTask.of_time run).bound 12 20 <;> intro i
  · simp only [cuts,size_prod,cutSizes,size_tally,tally_length,V]; ring_nf; omega
  · change size (hdr i,xs i)+((rows i+1)*size (tally (width i))+size (cuts i,xs i))+1 ≤ _
    simp only [cuts,hdr,size_prod,cutSizes,size_tally,tally_length,V]; ring_nf; omega

/-- All the coefficient words for one fixed prefix form a single bitstring. -/
def row {w : ℕ} (g : List (Dusk.Grain w)) := g.flatMap word

@[simp] theorem row_length {w : ℕ} (g : List (Dusk.Grain w)) :
    (row g).length = g.length*(2*(w+1)) := by
  induction g with
  | nil => simp [row]
  | cons x xs ih => simp only [row, List.flatMap_cons, List.length_append, word_length,
      List.length_cons, Nat.succ_mul] at *; omega

private theorem flat_words {w : ℕ} (gs : List (List (Dusk.Grain w))) :
    (gs.flatten.map word).flatten = (gs.map row).flatten := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.flatten_cons,List.map_append,List.flatten_append,
      List.map_cons,ih,row,List.flatMap_def]

private theorem count_flat {Z : Type} (gs : List (List Z)) (b : ℕ)
    (h : ∀ x ∈ gs, x.length = b) : gs.flatten.length = gs.length*b := by
  induction gs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,hs⟩ := List.forall_mem_cons.mp h
    simp only [List.flatten_cons,List.length_append,List.length_cons,ih hs,hx,Nat.succ_mul]
    omega

private theorem bitrows_size (gs : List (List Bool)) (b : ℕ)
    (h : ∀ x ∈ gs, x.length = b) : size gs = gs.length*(2*b+2)+1 := by
  induction gs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,hs⟩ := List.forall_mem_cons.mp h
    simp only [size_cons,Bits.size_word,hx,ih hs,List.length_cons,Nat.succ_mul]
    omega

variable (b : I → ℕ) (gs : (i : I) → List (List (Dusk.Grain (w i))))
    (uniform : ∀ i g, g ∈ gs i → g.length = b i)

include uniform

private theorem row_width (i : I) (bits : List Bool) (h : bits ∈ (gs i).map row) :
    bits.length = b i*(2*(w i+1)) := by
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp h
  rw [row_length,uniform i g hg]

/-- Group contiguous coefficient records into the uniform bitstring payload
for one swap row. The input header contains exactly two tally rulers. -/
theorem pack :
    let n i := (gs i).length
    let V i := (n i+1)*(b i+1)*(w i+1)
    BoundedTask V V
      (fun i => send ((tally (n i),tally (b i*(2*(w i+1)))),(gs i).flatten.map Dusk.mark))
      (fun i => send ((gs i).map row)) := by
  intro n V
  let hdr i := (tally (n i),tally (b i*(2*(w i+1))))
  have map : Easy (fun p : (Tally × Tally) × List Dusk.Pair => (p.1,p.2.map encode)) :=
    Easy.fst.pair (Easy.snd.compose encode_easy.mapping)
  let raw i := (gs i).flatten
  have pre := map.on (fun i => (hdr i,(raw i).map Dusk.mark))
  simp only [List.map_map] at pre
  have run := reshape n (fun i => b i*(2*(w i+1))) (fun i => (raw i).map word)
    (fun i => (gs i).map row) (fun i => flat_words _) (fun i => List.length_map row)
    (row_width w b gs uniform)
  have step := (BoundedTask.of_time pre).compose run
  apply step.bound 32 48 <;> intro i
  all_goals
    simp only [send_count,size_prod,hdr,size_tally,tally_length,words_size,
      PhysicalWalsh.Padding.marks_size,raw,count_flat _ _ (uniform i),V,n]
  · ring_nf; omega
  · rw [← max_add_add_right]; apply max_le <;> ring_nf <;> omega

/-- Restore the original record boundaries after any permutation of entire
packed rows. The two tallies are the total record count and record bit width. -/
theorem unpack :
    let n i := (gs i).length
    let V i := (n i+1)*(b i+1)*(w i+1)
    BoundedTask V V
      (fun i => send ((tally (n i*b i),tally (2*(w i+1))),(gs i).map row))
      (fun i => send ((gs i).flatten.map Dusk.mark)) := by
  intro n V
  let raw i := (gs i).flatten
  have split := reshape (fun i => n i*b i) (fun i => 2*(w i+1))
    (fun i => (gs i).map row) (fun i => (raw i).map word) (fun i => (flat_words _).symm)
    (fun i => by simp only [List.length_map,raw,count_flat _ _ (uniform i),n])
    (fun _ _ h => by obtain ⟨v,_,rfl⟩ := List.mem_map.mp h; exact word_length v)
  have decoded := decodeRows w raw
  apply (split.compose decoded).bound 20 24 <;> intro i
  all_goals
    simp only [bitrows_size _ _ (row_width w b gs uniform i),List.length_map,raw,count_flat _ _ (uniform i),V,n]
  · ring_nf; omega
  · rw [← max_add_add_right]; apply max_le <;> ring_nf <;> omega

omit uniform

/-- The suffix of an ordinal record remains in place inside its swap payload. -/
def payload {w : ℕ} (b : ℕ) (x : ℕ → Dusk.Grain w) (n : ℕ) :=
  ((List.range b).map (fun j => word (x (n*b+j)))).flatten

private def block {Z : Type} (b : ℕ) (x : ℕ → Z) (n : ℕ) :=
  (List.range b).map (fun j => x (n*b+j))

private def blocks {Z : Type} (n b : ℕ) (x : ℕ → Z) := (List.range n).map (block b x)

private theorem block_length {Z : Type} (b : ℕ) (x : ℕ → Z) (j : ℕ) :
    (block b x j).length = b := by simp [block]

private theorem flatten_blocks {Z : Type} (n b : ℕ) (x : ℕ → Z) :
    (blocks n b x).flatten = (List.range (n*b)).map x := by
  induction n with
  | zero => simp [blocks]
  | succ n ih =>
    rw [blocks,List.range_succ,List.map_append,List.flatten_append]
    rw [← blocks,ih,Nat.succ_mul,List.range_add]
    simp [block,List.map_map,Function.comp_def]

private theorem rows_blocks {w} (n b) (x : ℕ → Dusk.Grain w) :
    (blocks n b x).map row = (List.range n).map (payload b x) := by
  simp only [blocks,List.map_map,row,block,List.flatMap_def,Function.comp_def]
  rfl

@[simp] theorem payload_length {w} (b) (x : ℕ → Dusk.Grain w) (n) :
    (payload b x n).length = b*(2*(w+1)) := by
  have h := row_length (block b x n)
  simpa only [block,row,List.flatMap_def,List.map_map,payload,Function.comp_def,
    List.length_map,List.length_range] using h

noncomputable def payloadBeads {w : ℕ} (b : ℕ) (x : ℕ → Dusk.Grain w) (n : ℕ) :
    Fin (b*(2*(w+1))) → Bead :=
  bitstringBeads (payload b x n) (payload_length b x n)

@[simp] theorem strip_payload {w : ℕ} (b : ℕ) (x : ℕ → Dusk.Grain w) (n : ℕ) :
    strip (Series.natural (b*(2*(w+1)))) (payloadBeads b x n) = send (payload b x n) :=
  strip_bitstring _ _

private theorem block_uniform {Z : Type} (n b : ℕ) (x : ℕ → Z) (v : List Z)
    (h : v ∈ blocks n b x) : v.length=b := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
  exact block_length ..

private theorem reduced_charge {n b w : ℕ} (hn : 0 < n) (hb : 0 < b) :
    (n+1)*(b+1)*(w+1)+1 ≤ 4*((n*b+1)*(w+1)+1) := by
  have ge : (n+1)*(b+1) ≤ 4*(n*b+1) := by
    have := Nat.le_mul_of_pos_left b hn
    have := Nat.le_mul_of_pos_right n hb
    rw [Nat.add_mul,Nat.mul_add]; omega
  have h := Nat.mul_le_mul_right (w+1) ge
  rw [Nat.mul_assoc 4] at h
  omega

variable (n : I → ℕ) (r : (i : I) → ℕ → Dusk.Grain (w i))

/-- A permutation of the high ordinal acts on complete suffix payloads. -/
theorem payload_map {w b : ℕ} (hb : 0 < b) (x : ℕ → Dusk.Grain w) (f : ℕ → ℕ) (n : ℕ) :
    payload b (fun k => x (f (k/b)*b+k%b)) n = payload b x (f n) := by
  unfold payload
  congr 1
  apply List.map_congr_left
  intro j hj
  have bound := List.mem_range.mp hj
  dsimp only
  rw [show (n*b+j)/b = n from by
    rw [Nat.mul_comm n b,Nat.mul_add_div hb,Nat.div_eq_of_lt bound,Nat.add_zero],Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt bound]

/-- Convert the flat physical stream into rows indexed by the high ordinal.
Each row contains all of its suffix records in their existing order. -/
theorem packOrdinal (hn : ∀ i, 0 < n i) (hb : ∀ i, 0 < b i) :
    let V i := (n i*b i+1)*(w i+1)
    BoundedTask V V
      (fun i => send ((tally (n i),tally (b i*(2*(w i+1)))),
        (List.range (n i*b i)).map (Dusk.mark ∘ r i)))
      (fun i => send ((List.range (n i)).map (payload (b i) (r i)))) := by
  intro V
  have run := pack w b (fun i => blocks (n i) (b i) (r i))
    (fun i => block_uniform (n i) (b i) (r i))
  have len i : (blocks (n i) (b i) (r i)).length = n i := by simp [blocks]
  simp only [len,flatten_blocks,rows_blocks,List.map_map] at run
  exact run.bound 4 4 (fun i => reduced_charge (hn i) (hb i))
    (fun i => reduced_charge (hn i) (hb i))

/-- Convert packed bitstring rows back to the flat physical Walsh stream. -/
theorem unpackOrdinal (hn : ∀ i, 0 < n i) (hb : ∀ i, 0 < b i) :
    let V i := (n i*b i+1)*(w i+1)
    BoundedTask V V
      (fun i => send ((tally (n i*b i),tally (2*(w i+1))),
        (List.range (n i)).map (payload (b i) (r i))))
      (fun i => send ((List.range (n i*b i)).map (Dusk.mark ∘ r i))) := by
  intro V
  have run := unpack w b (fun i => blocks (n i) (b i) (r i))
    (fun i => block_uniform (n i) (b i) (r i))
  have len i : (blocks (n i) (b i) (r i)).length = n i := by simp [blocks]
  simp only [len,flatten_blocks,rows_blocks,List.map_map] at run
  exact run.bound 4 4 (fun i => reduced_charge (hn i) (hb i))
    (fun i => reduced_charge (hn i) (hb i))

end PhysicalWalshSwapCodec

end NearSquareRoot
end Computability
end OAI
