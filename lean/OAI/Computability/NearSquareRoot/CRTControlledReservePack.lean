import OAI.Computability.NearSquareRoot.CRTControlledReserveTile
import OAI.Computability.NearSquareRoot.CRTControlledReserveRulers
import OAI.Computability.NearSquareRoot.CRTControlledRowStreams
import OAI.Computability.NearSquareRoot.CRTControlledBudget

/-! # Packing the low address suffix into each middle record -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReservePack
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Loom

variable {X Z : Type} [Codec Z] {S T U : X → Type}
variable (s : (x : X) → Series (S x)) (t : (x : X) → Series (T x)) (u : (x : X) → Series (U x))
variable (v : (x : X) → S x × T x → U x → Z)

/-- A physical list of original records, each storing its own symbol strip. -/
def cells := stackRun (fun x => (s x).cart (t x)) (fun x a => strip (u x) (v x a))

/-- Each outer record holds all symbols of its complete low suffix, in order. -/
def packedCells := stackRun s fun x a => strip ((t x).cart (u x)) (fun z => v x (a,z.1) z.2)

variable {w : X → ℝ} {src : X → Tree}

theorem carveLow (data : Carries w src (cells s t u v))
    (dims : Carries w src (fun x => rulers (s x) (t x)))
    (geometry : ∃ E : ℕ, ∀ x, ((s x).count + 1 : ℝ) * ((t x).count + 1) ≤ E * w x) :
    Carries w src (packedCells s t u v) := by
  let vals x := (s x).tab (fun a => (t x).tab (fun b => (u x).tab (v x (a,b))))
  have body := Strip.carve s t (fun x a => strip (u x) (v x a)) data dims geometry
  change Carries w src (fun x => stripe (s x) (fun a => stripe (t x) (fun b => strip (u x) (v x (a,b))))) at body
  simp only [strip, stripe_eq'] at body
  have flat := Carries.func (y := vals) body.budget body.out
    (List.map (List.flatten (α := Z))) Easy.flatten.mapping
  apply body.chain
  convert flat using 1
  funext x
  simp only [packedCells, stackRun, strip, stripe_eq', vals, Series.grouped, Series.map_tab]
  rfl

theorem restoreLow (data : Carries w src (packedCells s t u v))
    (dims : Carries w src (fun x => rulers ((s x).cart (t x)) (u x)))
    (geometry : ∃ E : ℕ, ∀ x, (((s x).cart (t x)).count + 1 : ℝ) * ((u x).count + 1) ≤ E * w x) :
    Carries w src (cells s t u v) := by
  let leaf x (a : S x × (T x × U x)) := send (v x (a.1,a.2.1) a.2.2)
  have flat := Strip.flatten s (fun x => (t x).cart (u x)) leaf data
  have flat' : Carries w src (fun x => stripe (((s x).cart (t x)).cart (u x))
      (fun a => send (v x a.1 a.2))) := by
    convert flat using 1
    funext x
    exact ((Adopt.rotate (s x) (t x) (u x)).packet (leaf x)).symm
  exact Strip.carve (fun x => (s x).cart (t x)) u (fun x a => send (v x a.1 a.2))
    flat' dims geometry

/-- The physical record and symbol rulers can be sampled before running the
middle program, including when the symbol width exceeds the header scale. -/
theorem readRulers (nonempty : ∀ x, 0 < ((s x).cart (t x)).count)
    (data : Carries w src (cells s t u v)) :
    Carries w src (fun x => rulers ((s x).cart (t x)) (u x)) := by
  let rows x := ((s x).cart (t x)).tab (fun a => (u x).tab (v x a))
  have d : Carries w src (fun x => send (rows x)) := by
    change Carries w src (fun x => stripe ((s x).cart (t x)) (fun a => strip (u x) (v x a))) at data
    simpa only [strip, stripe_eq', rows] using data
  let sample (l : List (List Z)) := (ruler l, ruler (l.headD []))
  have e : Easy sample := by unfold sample; fun_prop
  apply d.chain
  convert Carries.func (y := rows) d.budget d.out sample e using 1
  funext x
  have top : (rows x).length = ((s x).cart (t x)).count := Series.card ..
  have first : ((rows x).headD []).length = (u x).count := by
    obtain ⟨a,ls,hs⟩ := List.exists_cons_of_ne_nil (l := rows x) (fun h => by
      have := nonempty x; rw [h, List.length_nil] at top; omega)
    have ha : a ∈ rows x := hs ▸ List.mem_cons_self
    obtain ⟨b,hb⟩ := (Series.elements ..).mp ha
    simp only [hs, List.headD_cons, ← hb, Series.card]
  have tallyR {Y : Type} (l : List Y) : ruler l = tally l.length := by
    rw [← ruler_length l]
    exact (recover_tally _).symm
  simp only [sample, send_prod, tallyR, top, first]

variable (n B : X → ℕ)
variable (f : (x : X) → Block 2 (n x + B x) → U x → Z)

def raw := stackRun (fun x => line 2 (n x + B x)) (fun x a => strip (u x) (f x a))

def grouped := stackRun (fun x => line 2 (n x)) fun x a =>
  strip ((line 2 (B x)).cart (u x)) (fun z => f x ((prefixView rfl).cast (a,z.1)) z.2)

private def localData (x : X) (a : Block 2 (n x) × Block 2 (B x)) := f x ((prefixView rfl).cast a)

private theorem raw_cells : raw u n B f =
    cells (fun x => line 2 (n x)) (fun x => line 2 (B x)) u (localData n B f) := by
  funext x
  exact (prefixView (p := n x) (n := B x) rfl).packet _

/-- The globally grouped suffix and the high-row middle view place all fields at
the same physical address. -/
theorem tile_assoc {k lo hi : ℕ} (fit : lo + hi ≤ k) (h : Block 2 hi)
    (a : Block 2 (k - lo - hi)) (b : Block 2 lo) :
    (prefixView (p := hi + (k-lo-hi)) (n := lo) (k := k) (by omega)).cast
      ((prefixView rfl).cast (h,a),b) = (ReserveTile.view fit).cast (h,a,b) := by
  apply distinct 2 k
  apply List.reverse_injective
  change least _ = least _
  change least ((prefixView _).cast ((prefixView rfl).cast (h,a),b)) =
    least ((prefixView _).cast (h,(prefixView rfl).cast (a,b)))
  simp only [prefixView_least, List.append_assoc]

/-- The row program sees one record per middle address. -/
abbrev records (n : X → ℕ) (x : X) := 2 ^ n x

/-- The computational payload width includes all low addresses. -/
abbrev packed (B m : X → ℕ) (x : X) := 2 ^ B x * m x

def restoreRulers (x : X) := rulers ((line 2 (n x)).cart (line 2 (B x))) (u x)

private theorem bounds {a b M V : ℕ} (ha : 0 < a) (hm : 0 < M) (hb : b ≤ M)
    (vol : a * M ≤ V) : (a + 1) * (b + 1) ≤ 4 * V := by
  calc
    _ ≤ (2 * a) * (2 * M) := Nat.mul_le_mul (by omega) (by omega)
    _ = 4 * (a * M) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ vol

variable {r : Regime X} (m : X → ℕ) (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x)

include hm hu in
theorem raw_alive (C : ℕ) (symbol : ∀ x a i, (send (f x a i)).count ≤ C) :
    Alive r (records n) (packed B m) (raw u n B f) := by
  refine ⟨0, Carries.idles (unit_mass (fun _ => Nat.two_pow_pos _) _) ⟨C + 4, fun x => ?_⟩⟩
  have leaf (a) : (strip (u x) (f x a)).count ≤ m x * (C+3) := by
    apply (stripe_size _ _ C (symbol x a)).trans
    have big := Nat.mul_le_mul_right (C+1) (hu x)
    calc
      _ ≤ m x * (C+1) + 1 := Nat.add_le_add_right big 1
      _ ≤ m x * (C+1) + m x * 2 := by have := hm x; omega
      _ = _ := by ring
  have h := stripe_size (line 2 (n x+B x)) _ _ leaf
  change (raw u n B f x).count ≤ _ at h
  rw [lineSize, pow_add] at h
  have bound : (raw u n B f x).count ≤ (C+4) * (2^n x * (2^B x * m x + 1)) := by
    let N := 2^n x
    let T := 2^B x
    have ht := hm x
    have hp : 0 < N*T := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    have hs : 1 ≤ N := Nat.two_pow_pos _
    change (raw u n B f x).count ≤ N*T*(m x*(C+3)+1)+1 at h
    change _ ≤ (C+4)*(N*(T*m x+1))
    have v := Nat.le_mul_of_pos_right (N*T) ht
    nlinarith only [h,v,hs,Nat.zero_le (C*N)]
  simpa only [mass, pow_zero, records, packed, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr bound

include hm in
private theorem geometry {r : Regime X} (d : ℕ) (x : X) :
    ((line 2 (n x)).count + 1 : ℝ) * ((line 2 (B x)).count + 1) ≤
      4 * mass r (records n) (packed B m) d x := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (mass_le (r := r) (n := records n)
    (l := packed B m) (Nat.zero_le d) x) (by norm_num))
  simp only [mass, pow_zero, records, packed, lineSize]
  exact_mod_cast bounds (a := 2^n x) (b := 2^B x) (M := 2^B x) (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    le_rfl (Nat.mul_le_mul_left _ (by have h := Nat.le_mul_of_pos_right (2^B x) (hm x); omega))

include hm hu in
private theorem geometry_restore {r : Regime X} (d : ℕ) (x : X) :
    (((line 2 (n x)).cart (line 2 (B x))).count + 1 : ℝ) * ((u x).count + 1) ≤
      4 * mass r (records n) (packed B m) d x := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (mass_le (r := r) (n := records n)
    (l := packed B m) (Nat.zero_le d) x) (by norm_num))
  simp only [mass, pow_zero, records, packed, Series.count_cart, lineSize]
  exact_mod_cast bounds (a := 2^n x * 2^B x) (b := (u x).count) (M := m x)
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) (hm x) (hu x)
    (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_succ _))

variable (hn : r.Has (tally ∘ n)) (hB : r.Has (tally ∘ B))

include hm hn hB in
/-- Carve the low suffix, emit the requested middle-program header, and save
the two rulers needed to restore arbitrary original record widths. -/
theorem prepare {head : X → Tree} (hh : r.Small head)
    (live : Alive r (records n) (packed B m) (raw u n B f)) :
    Drive r (records n) (packed B m) (raw u n B f)
      (together (restoreRulers u n B) (together head (grouped u n B f))) := by
  let s x := line 2 (n x)
  let t x := line 2 (B x)
  have pos (x : X) : 1 ≤ records n x := Nat.two_pow_pos _
  have roomT (x : X) : 2^B x ≤ records n x * (packed B m x + 1) :=
    (Nat.le_mul_of_pos_right _ (hm x)).trans
      ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (pos x)))
  have roomS (x : X) : 2^n x ≤ records n x * (packed B m x + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have ds := (ReserveRulers.binary hn pos roomS).twice (ReserveRulers.binary hB pos roomT)
  have dims : Rip r (records n) (packed B m) r.header (fun x => rulers (s x) (t x)) := by
    change Rip r _ _ r.header (fun x => Tree.fork (send (tally (s x).count)) (send (tally (t x).count)))
    simpa only [s,t,lineSize] using ds
  have dc := (Drive.fetch pos live).chain dims
  have physical := Drive.self pos live
  obtain ⟨a,rawData⟩ := physical
  have data := (congrArg (Carries (mass r (records n) (packed B m) a)
    (together r.header (raw u n B f))) (raw_cells u n B f)).mp rawData
  obtain ⟨b,rules⟩ := dc
  have stored := readRulers s t u (localData n B f)
    (fun x => by simp only [s,t,Series.count_cart,lineSize]; positivity) data
  have groupedRun := carveLow s t u (localData n B f)
    (data.larger
      (mass_le (r := r) (n := records n) (l := packed B m) (by omega : a ≤ a+b)))
    (rules.larger (mass_le (by omega : b ≤ a+b)))
    ⟨4, geometry (r := r) n B m hm (a+b)⟩
  exact (show Drive r (records n) (packed B m) _ _ from ⟨a, stored⟩).twice
    ((Drive.small pos live hh).twice (show Drive r (records n) (packed B m) _ _ from ⟨a+b, groupedRun⟩))

include hm hu hn hB in
/-- The restored row has exactly the original physical format. The width ruler
is sampled from its first input record and retained through the middle pass. -/
theorem around (g : (x : X) → Block 2 (n x + B x) → U x → Z)
    {head : X → Tree} (hh : r.Small head) (C : ℕ) (symbol : ∀ x a i, (send (f x a i)).count ≤ C)
    {rate : X → ℝ}
    (middle : Breeze rate r (records n) (packed B m) (together head (grouped u n B f)) (grouped u n B g)) :
    Breeze rate r (records n) (packed B m) (together r.header (raw u n B f)) (raw u n B g) := by
  obtain ⟨positive,d,core⟩ := middle
  have live := raw_alive (r := r) u n B f m hm hu C symbol
  obtain ⟨j,prep⟩ := prepare u n B f m hm hn hB hh live
  let D := d+j
  have init := prep.larger fun x => (mass_le (by omega : j ≤ D) x).trans
    (le_mul_of_one_le_right (by unfold mass; positivity) (positive x))
  have body := (core.larger (fun x => rate_higher x (positive x) (by omega : d ≤ D))).second
    (Volume.left init.out)
  have done_ := init.chain body
  have left := done_.chain (Carries.dropRight done_.budget (Volume.left done_.out) (Volume.right done_.out))
  have right := done_.chain (Carries.dropLeft done_.budget (Volume.left done_.out) (Volume.right done_.out))
  refine ⟨positive,D,?_⟩
  rw [raw_cells u n B g]
  apply restoreLow (fun x => line 2 (n x)) (fun x => line 2 (B x)) u (localData n B g) right left
  refine ⟨4, fun x => (geometry_restore (r := r) u n B m hm hu D x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_right (by unfold mass; positivity) (positive x)) (by norm_num)

/-- The original row volume measured in ungrouped payload symbols. -/
def volume (n B m : X → ℕ) (x : X) : ℕ := records n x * packed B m x

include hm hu hn hB in
/-- The degree is chosen before selecting a concrete row family. After absorbing
header work into the low suffix, preparation takes linear time and space. -/
theorem prepareBoundedOn {head : X → Tree} (hh : r.Small head) (C : ℕ)
    (symbol : ∀ x a i, (send (f x a i)).count ≤ C) :
    ∃ d : ℕ, ∀ {Y : Type} (select : Y → X) (Q : Y → ℕ),
      (∀ y, r.scale (select y) ≤ Q y) → (∀ y, payloadBits d (Q y) ≤ B (select y)) →
      Space.BoundedTask (volume n B m ∘ select) (volume n B m ∘ select)
        (together r.header (raw u n B f) ∘ select)
        (together (restoreRulers u n B) (together head (grouped u n B f)) ∘ select) := by
  obtain ⟨d,pre⟩ := prepare u n B f m hm hn hB hh (raw_alive u n B f m hm hu C symbol)
  refine ⟨d, fun select Q scale low => ?_⟩
  apply boundedOfCarries
  apply (pre.slide select).times _ 2
  · intro y
    change (records n (select y) : ℝ) * ((packed B m (select y) : ℕ) + _) ≤ _
    have cap : (r.scale (select y)+1)^d ≤ packed B m (select y) :=
      (Nat.pow_le_pow_left (Nat.succ_le_succ (scale y)) d).trans
        ((payload_capacity d (Q y) (m (select y)) (hm _)).trans
          (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (low y))))
    have cap' : (r.scale (select y)+1 : ℝ)^d ≤ packed B m (select y) := by exact_mod_cast cap
    change _ ≤ 2 * ((records n (select y) * packed B m (select y) : ℕ) : ℝ)
    have h := mul_le_mul_of_nonneg_left cap' (Nat.cast_nonneg (α := ℝ) (records n (select y)))
    simp only [records, packed, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    linarith
  · intro y
    have := hm (select y)
    change (1 : ℝ) ≤ (2^n (select y) * (2^B (select y) * m (select y)) : ℕ)
    exact_mod_cast Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _) this)

include hm hu in
/-- The stored record and symbol rulers suffice to unpack the output in linear
time and space, independently of the size or cost of the middle program. -/
theorem restoreBounded (C : ℕ) (symbol : ∀ x a i, (send (f x a i)).count ≤ C) :
    Space.BoundedTask (volume n B m) (volume n B m)
      (together (restoreRulers u n B) (grouped u n B f)) (raw u n B f) := by
  let w (x : X) : ℝ := volume n B m x
  have pos (x : X) : 0 < volume n B m x :=
    Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _) (hm x))
  have wp (x : X) : 1 ≤ w x := by
    dsimp only [w]
    exact_mod_cast (show 1 ≤ volume n B m x from pos x)
  have addr (x : X) : 2^n x * 2^B x ≤ volume n B m x := by
    unfold volume records packed
    rw [← Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (hm x)
  have bead (x : X) : (u x).count ≤ volume n B m x :=
    (hu x).trans ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)))
  have rv : Volume w (restoreRulers u n B) := by
    refine ⟨7,fun x => ?_⟩
    have h : (restoreRulers u n B x).count ≤ 7 * volume n B m x := by
      change size (tally _) + size (tally _) + 1 ≤ _
      simp only [size_tally, tally_length, Series.count_cart, lineSize]
      have a := addr x
      have b := bead x
      have p := pos x
      omega
    dsimp only [w]
    exact_mod_cast h
  have gv : Volume w (grouped u n B f) := by
    refine ⟨C+4, fun x => ?_⟩
    let p := packed B m x
    let N := records n x
    have hp : 0 < p := Nat.mul_pos (Nat.two_pow_pos _) (hm x)
    have hN : 0 < N := Nat.two_pow_pos _
    have leaf (a) :
        (strip ((line 2 (B x)).cart (u x))
          (fun z => f x ((prefixView rfl).cast (a,z.1)) z.2)).count ≤ p*(C+1)+1 := by
      apply (stripe_size _ _ C (fun _ => symbol ..)).trans
      simp only [Series.count_cart, lineSize]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hu x))) _
    have hh := stripe_size (line 2 (n x)) _ _ leaf
    change (grouped u n B f x).count ≤ _ at hh
    rw [lineSize] at hh
    have hn : N ≤ N*p := Nat.le_mul_of_pos_right _ hp
    change (grouped u n B f x).count ≤ N*(p*(C+1)+1+1)+1 at hh
    have bound : (grouped u n B f x).count ≤ (C+4)*(N*p) := by nlinarith
    change (grouped u n B f x).count ≤ (((C+4 : ℕ) : ℝ) * ((N*p : ℕ) : ℝ))
    exact_mod_cast bound
  have left := Carries.dropRight wp rv gv
  have right := Carries.dropLeft wp rv gv
  apply boundedOfCarries
  rw [raw_cells u n B f]
  apply restoreLow (fun x => line 2 (n x)) (fun x => line 2 (B x)) u (localData n B f) right left
  refine ⟨4, fun x => ?_⟩
  simp only [Series.count_cart, lineSize]
  have h := bounds (a := 2^n x * 2^B x) (b := (u x).count) (M := m x)
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) (hm x) (hu x)
    (show 2^n x * 2^B x * m x ≤ volume n B m x by simp only [volume,records,packed,Nat.mul_assoc,le_refl])
  dsimp only [w]
  exact_mod_cast h

end Controlled.ReservePack

end NearSquareRoot
end Computability
end OAI
