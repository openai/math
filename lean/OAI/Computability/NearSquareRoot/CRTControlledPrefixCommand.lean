import OAI.Computability.NearSquareRoot.CRTControlledPrefixNamedRate
import OAI.Computability.NearSquareRoot.CRTControlledPrefixPrepare

/-! # Named physical routing under a binary prefix

Two unary lengths accompany the shared header on entry. The command carves
out each low-field array, passes its original header to the supplied opcode,
and concatenates the returned rows in their original high-field order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PrefixCommand

open IntegerMultiplication Code Strip Loom Adic NamedPacked CommonRegisters GeneratorSyntax Filter

/-- Only the inner opcode varies among candidates with the same header type. -/
noncomputable def command (H : Type) [Codec H] (inner : Cmd) :=
  (prepare H).join ((NamedLiftoff.rowMap inner).join flattenCmd)

theorem command_effective (H : Type) [Codec H] {J : Type} [Primcodable J] {inner : J → Cmd}
    (h : Effective ltr inner) : Effective ltr (fun j => command H (inner j)) :=
  (effective_const ltr _).join ((NamedLiftoff.effective inner h).join (effective_const ltr _))

theorem command_within (H : Type) [Codec H] (R : ℕ) : ∃ S, 0 < S ∧ ∀ c, Within R c → Within S (command H c) := by
  obtain ⟨S,hS,hp,hf⟩ := ((eventually_gt_atTop (max 3 R)).and
    ((RegisterSelect.within_eventually (prepare H)).and (RegisterSelect.within_eventually flattenCmd))).exists
  exact ⟨S,by omega,fun c hc => ⟨hp,RegisterSelect.within_mono hS.le _ (NamedLiftoff.within hc),hf⟩⟩

/-- Physically group an arbitrary tree-valued rectangular array. Each inner
invocation sees the same shared header and a whole contiguous low-digit row. -/
theorem prefixPass {X H : Type} [Codec H] {r : Regime X} {width : X → ℕ} {rate : X → ℝ}
    (p n : X → ℕ) (head : X → H) (hp : r.Has (tally ∘ p)) (hn : r.Has (tally ∘ n))
    (hh : r.Has head) (hr : ∀ i,1 ≤ rate i)
    (src dst : (i : X) → Block 2 (p i) × Block 2 (n i) → Tree)
    (cell : ∀ i a, (src i a).count ≤ 2*width i+1) {inner : Cmd}
    (step : BreezeAt inner (fun z : (i : X) × Block 2 (p i) => rate z.1) (r.pull Sigma.fst)
      (fun z => (line 2 (n z.1)).count) (fun z => width z.1)
      (fun z => .fork (send (head z.1)) (stripe (line 2 (n z.1)) (fun b => src z.1 (z.2,b))))
      (fun z => stripe (line 2 (n z.1)) (fun b => dst z.1 (z.2,b)))) :
    let whole i := (line 2 (p i)).cart (line 2 (n i))
    BreezeAt (command H inner) rate r (fun i => (whole i).count) width
      (together (fun i => send ((tally (p i),tally (n i)),head i)) (stackRun whole src)) (stackRun whole dst) := by
  intro whole
  let z (i : X) : World H := ⟨p i,n i,width i,head i,src i,cell i⟩
  let key (i : X) := size (descriptor (z i))
  let N (i : X) := (whole i).count
  have dom : Dom r.scale key := ((hp.pair hn).pair hh).extent
  have ps := Adic.terminal (p := 2) (by decide) p hp
  have ns := Adic.terminal (p := 2) (by decide) n hn
  have pn (i : X) : 1 ≤ N i := (ps.product ns).1 i
  obtain ⟨d,C,hC⟩ := rebase (n := N) (w := width) key dom (degree H)
  let G := runrate rate r N width d
  have gpos i : 1 ≤ G i := one_le_mul_of_one_le_of_one_le (unit_mass pn d i) (hr i)
  have fit i : mass (regime H) count World.w (degree H) (z i) ≤ (C:ℝ)*G i :=
    (hC i).trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (zero_le_one.trans (unit_mass pn d i)) (hr i)) (Nat.cast_nonneg C))
  have front := reprice ((preparedAt H).on z) C gpos fit
  have a : BreezeAt (prepare H) rate r N width (input ∘ z) (output ∘ z) := ⟨hr,d,front⟩
  exact a.next (rowPass _ _ r width rate ps.1 ns.1 hr (send ∘ head) src dst step)

/-- The low field may have a different rank at every physical invocation.
The variation in ranks is encoded by two unary fields on the input packet. -/
theorem binaryPrefixPassFor {X H : Type} [Codec H] {r : Regime X} {width : X → ℕ} {rate : X → ℝ}
    (p n k : X → ℕ) (eq : ∀ i,p i+n i=k i) (head : X → H) (key : ∀i,r.header i=send (head i))
    (hp : r.Has (tally ∘ p)) (hn : r.Has (tally ∘ n)) (hr : ∀ i,1 ≤ rate i)
    {U : X → Type} (u : (i : X) → Series (U i)) (hu : ∀i,(u i).count ≤ width i)
    (move : (i : X) → Block 2 (n i) → Block 2 (n i)) {c : Cmd}
    (f : (i : X) → Block 2 (k i) → U i → Bead)
    (inner : let fs := fun (z : (i : X) × Block 2 (p i)) a => f z.1 ((prefixView (eq z.1)).cast (z.2,a))
      let ys := fun (z : (i : X) × Block 2 (p i)) => line 2 (n z.1)
      let rr := r.pull (Sigma.fst : ((i : X) × Block 2 (p i)) → X)
      let su := fun z : (i : X) × Block 2 (p i) => u z.1
      BreezeAt c (fun z => rate z.1) rr (fun z => (ys z).count) (fun z => width z.1)
        (together rr.header (cloth ys su fs)) (cloth ys su (fun z a => fs z (move z.1 a))))
    :
    let flat i := line 2 (k i)
    BreezeAt (command H c) rate r (fun i => (flat i).count) width
      (together (fun i => send ((tally (p i),tally (n i)),head i)) (cloth flat u f))
      (cloth flat u (fun i a => f i (underPrefix (eq i) (move i) a))) := by
  intro flat
  let P i := line 2 (p i)
  let T i := line 2 (n i)
  let C i := (P i).cart (T i)
  let v i := prefixView (eq i)
  let fs := fun (z : (i : X) × Block 2 (p i)) a => f z.1 ((v z.1).cast (z.2,a))
  let inp := fun i (a : Block 2 (p i) × Block 2 (n i)) => strip (u i) (fs ⟨i,a.1⟩ a.2)
  let out := fun i (a : Block 2 (p i) × Block 2 (n i)) => strip (u i) (fs ⟨i,a.1⟩ (move i a.2))
  have hh : r.Has head := by
    change r.Small (send ∘ head)
    rw [show send ∘ head = r.header from (funext key).symm]
    exact Regime.self
  have run := prefixPass (width := width) p n head hp hn hh hr inp out (fun i a => (bulk (u i) _).trans (by have := hu i; omega))
    (by
      have h := inner
      change BreezeAt c _ (r.pull Sigma.fst) _ _
        (fun z : (i : X) × Block 2 (p i) => .fork (r.header z.1)
          (stripe (line 2 (n z.1)) (fun b => inp z.1 (z.2,b))))
        (fun z => stripe (line 2 (n z.1)) (fun b => out z.1 (z.2,b))) at h
      simpa only [key] using h)
  have put (q : (i:X) → Block 2 (k i) → U i → Bead) :
      cloth flat u q = cloth C u (fun i a => q i ((v i).cast a)) := by
    funext i; exact (v i).packet _
  rw [← funext (fun i => (v i).cost),put f,put]
  convert run using 1
  apply congrArg (stackRun C)
  funext i a
  change strip (u i) (f i (underPrefix (eq i) (move i) ((v i).cast a))) = _
  unfold underPrefix
  change strip (u i) (f i ((v i).cast (((v i).cast.symm ((v i).cast a)).1,move i ((v i).cast.symm ((v i).cast a)).2))) = _
  rw [Equiv.symm_apply_apply]

/-- A uniformly correct inner command applies to every input cloth. -/
theorem binaryPrefixPass {X H : Type} [Codec H] {r : Regime X} {width : X → ℕ} {rate : X → ℝ}
    (p n k : X → ℕ) (eq : ∀ i,p i+n i=k i) (head : X → H) (key : ∀i,r.header i=send (head i))
    (hp : r.Has (tally ∘ p)) (hn : r.Has (tally ∘ n)) (hr : ∀ i,1 ≤ rate i)
    {U : X → Type} (u : (i : X) → Series (U i)) (hu : ∀i,(u i).count ≤ width i)
    (move : (i : X) → Block 2 (n i) → Block 2 (n i)) {c : Cmd}
    (inner : ∀ fs : (z : (i : X) × Block 2 (p i)) → Block 2 (n z.1) → U z.1 → Bead,
      let ys := fun (z : (i : X) × Block 2 (p i)) => line 2 (n z.1)
      let rr := r.pull (Sigma.fst : ((i : X) × Block 2 (p i)) → X)
      let su := fun z : (i : X) × Block 2 (p i) => u z.1
      BreezeAt c (fun z => rate z.1) rr (fun z => (ys z).count) (fun z => width z.1)
        (together rr.header (cloth ys su fs)) (cloth ys su (fun z a => fs z (move z.1 a))))
    (f : (i : X) → Block 2 (k i) → U i → Bead) :
    let flat i := line 2 (k i)
    BreezeAt (command H c) rate r (fun i => (flat i).count) width
      (together (fun i => send ((tally (p i),tally (n i)),head i)) (cloth flat u f))
      (cloth flat u (fun i a => f i (underPrefix (eq i) (move i) a))) :=
  binaryPrefixPassFor p n k eq head key hp hn hr u hu move f (inner _)

end Controlled.PrefixCommand

end NearSquareRoot
end Computability
end OAI
