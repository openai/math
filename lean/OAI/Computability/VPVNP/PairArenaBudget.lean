import OAI.Computability.VPVNP.PairTraversalArena
import OAI.Computability.VPVNP.CompressorDescriptorSquare
import OAI.Computability.VPVNP.PairLinkSlack
import OAI.Computability.VPVNP.CursorBranchCommunication
import OAI.Computability.VPVNP.RAMFinite

/-!
# Native construction of the selected pair's DFS arena

Place the ordered argument rows and their dispatch tags after the
Appendix E directory. The final shared-bit array occupies the interval
between them. The real worker traces use a vanishing fraction of the
live group's budget, including the two probes and forty-seven
instructions allowed for an enclosing transfer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRoles

open Compression CursorBounds CursorNetwork Filter BurstRAM BurstRAM.PrivateRAM
open CompressorRecords TraversalRows DirectoryRun LocalHistory NetworkKernel

variable {w : ℕ}

private def Worker.clock : Worker w → ℕ
  | .leaf .. => 14
  | .fiber _ cap .. => 7*cap+25

private theorem worker_clock {W : Worker w} {m : Memory w} {rs : List (Report w)} (h : W.Run m rs) :
    ∀ r ∈ rs, r.events.length < Worker.clock W := by
  cases W <;> exact localSegment_event_bound ((runSegment_iff ..).mp h).1

private theorem segments_clock {ws : List (Worker w)} {m : Memory w} {rs : List (Report w)} {K : ℕ}
    (h : Segments ws m rs) (hk : ∀ W ∈ ws, Worker.clock W ≤ K) :
    ∀ r ∈ rs, r.events.length < K := by
  induction h with
  | nil => simp
  | @cons head tail m rs ss run rest ih =>
    intro r hr
    rcases List.mem_append.mp hr with pre | post
    · exact (worker_clock run r pre).trans_le (hk head List.mem_cons_self)
    · exact ih (fun W hW => hk W (List.mem_cons_of_mem _ hW)) r post

private theorem role_clock {offset cap base : ℕ} {ls : List TaggedLayer} {m : Memory w}
    {rs : List (Report w)} (h : RolePasses offset cap base ls m rs) :
    ∀ r ∈ rs, r.events.length < 12 := by
  induction h with
  | nil => simp
  | cons run rest ih =>
    intro r hr
    exact (List.mem_append.mp hr).elim (localSegment_event_bound ((runSegment_iff ..).mp run).1 r)
      (ih r)

private theorem workers_clock {A : Type*} {N Y : Network} {raw : Memory w}
    {limit : ℕ} (c : TermChain A N Y) (ords : ChainOrders c) (old : Order N.Site)
    (dirs : Directories raw limit c ords old) (cap previous base : ℕ) :
    ∀ W ∈ workers c ords old dirs cap previous base, Worker.clock W ≤ 7*cap+25 := by
  induction c generalizing previous base with
  | done => simp [workers]
  | more t rec tail ih =>
    intro W hW
    rcases List.mem_cons.mp hW with rfl | h
    · rfl
    · exact ih ords.2 ords.1 dirs.2 base _ _ h

private theorem probes_le (es : List (Event w)) : countProbes es ≤ es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [countProbes] <;> omega

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- Native role and row reports on each selected branch, given the actual
per-level preimage directories produced by the shrink and refresh passes.
The array and report budgets are derived from the cursor parameters. -/
theorem eventually_nativeArena (B : S.Templates) (u : PairExponents B.growthConstant)
    (F : DescriptorSpace.Shape) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {start : ℕ → ℕ} (hstart : PolynomiallyBounded start) {ε : ℝ} (hε : 0 < ε)
    (probeMargin : ℕ := 2) (tickMargin : ℕ := 47) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let w := wordBits b n
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        let data := B.records f hf T hT X
        let baseAddr := DescriptorSpace.endAddress
          (DescriptorSpace.cursorLayout F b S.steps u.θ (start n) n)
        ∀ (z : E.Choices) (m : Memory w),
          let Y := E.finalState z
          let ls := selectedLayers B f hf T hT X z
          let rowWords := words B.recordLimit ls
          let offset := rowWords + Y.totalWidth
          let vs := executeLevels B f hf T hT X z
          let c := E.termChain data z
          let ords := branchOrders E data z
          let old := siteOrder X
          baseAddr + 2*rowWords + Y.totalWidth < min (2^w) (start n + (processorCount b n)^2) ∧
          ∀ ds : (i : Fin vs.length) → LevelDirectory vs[i] m baseAddr,
            let dirs := selectedDirectories B f hf T hT X z m baseAddr ds
            let ws := Worker.leaf B.recordLimit baseAddr old.length ::
              workers c ords old dirs B.recordLimit baseAddr
                (address B.recordLimit baseAddr old.length)
            ∃ ts rs, RolePasses offset B.recordLimit baseAddr (selected B f hf T hT X z) m ts ∧
              Segments ws (after m (eventLog ts)) rs ∧
              let out := after m (eventLog (ts++rs))
              Reads w out offset B.recordLimit baseAddr (selected B f hf T hT X z) ∧
              AllRows w out B.recordLimit baseAddr baseAddr ls ∧
              (∀ r ∈ ts++rs, 1+r.probes+probeMargin ≤ liveBucket u.δ n ∧
                r.events.length+tickMargin ≤ n) ∧
              ((ts.length + rs.length + countProbes (eventLog (ts++rs)) : ℕ) : ℝ) <
                ε * (processorCount b n : ℝ) * liveBucket u.δ n := by
  let K := 2*(B.recordLimit+2)
  let C := (2*B.recordLimit+6)*(S.steps+2)
  let clock := 7*B.recordLimit+25
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  have hp := CursorRAM.bounded_positions b
  have hword := CursorRAM.eventual_word_room b hb' (hstart.add (hp.pow 2))
  have hd : (u.θ : ℝ) ≤ 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
    norm_num at h
    linarith only [h]
  filter_upwards [DescriptorSpace.eventually_selected_square F B u b hb K, hword,
    eventually_pairAccesses B u b hb C 1 hε, eventually_pairBurstSlack u probeMargin,
    eventually_ge_atTop ((clock+tickMargin+3)^2), eventually_ge_atTop 3]
    with n hs hw hbudget hslack hn hn₃
  intro base lanes labels hD hT A _ f hf w X T E data baseAddr z m Y ls size off vs c ords old
  have hh := hs (start n) labels hD hT A f hf z
  have foot := selected_words_le B f hf T hT X z
  change size ≤ (B.recordLimit+2)*Y.positions*B.growthConstant^T at foot
  have room : baseAddr + 2*size + Y.totalWidth < start n + (processorCount b n)^2 := by
    apply lt_of_le_of_lt _ hh
    change baseAddr+2*size+Y.totalWidth ≤ baseAddr +
      K*(X.positions+processorCount b n+Y.positions*B.growthConstant^T+Y.totalWidth)+1
    dsimp only [K]
    nlinarith only [foot,Nat.zero_le (B.recordLimit*(X.positions+processorCount b n+Y.totalWidth))]
  have hR : processorCount b n ≤ initialPositions b n :=
    (Nat.pow_le_pow_right Nat.zero_lt_two (addressBits_le_virtualBits b n hn₃)).trans
      (Nat.le_mul_of_pos_right _ (by omega : 0 < virtualBits b n))
  have fit := room.trans_le (Nat.add_le_add_left (Nat.pow_le_pow_left hR 2) _)
  have hfit := fit.trans hw
  refine ⟨lt_min hfit room, ?_⟩
  intro ds dirs ws
  obtain ⟨ts,rs,hrole,hrows,_,tags,rows,_,len,probes⟩ :=
    native_arena B f hf T hT X z baseAddr Y.totalWidth m ds hfit
  have hclock : ∀ r ∈ ts++rs, r.events.length < clock := by
    intro r hr
    rcases List.mem_append.mp hr with tag | row
    · exact (role_clock hrole r tag).trans_le (by dsimp [clock]; omega)
    · apply segments_clock hrows _ r row
      intro worker hW
      rcases List.mem_cons.mp hW with rfl | h
      · dsimp [Worker.clock,clock]; omega
      · exact workers_clock c ords old dirs B.recordLimit baseAddr _ _ h
  have clock' : clock+tickMargin ≤ n := by
    have := Nat.le_self_pow (by decide : 2 ≠ 0) (clock+tickMargin+3)
    omega
  have burst : clock+1+probeMargin ≤ liveBucket u.δ n := by
    have hc : (clock+tickMargin+3 : ℝ)^2 ≤ n := by exact_mod_cast hn
    have hsqrt : (clock+tickMargin+3 : ℝ) ≤ (n : ℝ)^(1/2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le hc
    exact_mod_cast (by linarith only [hsqrt,hslack, Nat.cast_nonneg (α := ℝ) tickMargin] :
      (clock : ℝ)+1+probeMargin ≤ (liveBucket u.δ n : ℝ))
  refine ⟨ts,rs,hrole,hrows,tags,rows,fun r hr => ?_,?_⟩
  · have he := hclock r hr
    have hp : r.probes ≤ r.events.length := probes_le _
    omega
  · let l := n.log2+1
    have ht : T ≤ l := by
      apply le_trans _ (BurstRAM.clog_le_log2_succ n)
      change ⌊(u.θ : ℝ)*Real.logb 2 n⌋₊ ≤ Nat.clog 2 n
      rw [← Real.natCeil_logb_natCast 2 n]
      apply (Nat.floor_le_floor (mul_le_of_le_one_left _ hd)).trans (Nat.floor_le_ceil _)
      exact Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
    have ht' : (S.steps+1)*T+1 ≤ (S.steps+2)*l := by
      have hmul := Nat.mul_le_mul_left (S.steps+1) ht
      have hl : 1 ≤ l := Nat.succ_pos _
      exact (Nat.add_le_add hmul hl).trans_eq (by ring)
    have hcost : ts.length+rs.length+countProbes (eventLog (ts++rs)) ≤ C*X.positions*l := by
      have h := Nat.add_le_add len probes
      calc _ ≤ (2*B.recordLimit+6)*(((S.steps+1)*T+1)*X.positions) := h.trans_eq (by ring)
           _ ≤ (2*B.recordLimit+6)*(((S.steps+2)*l)*X.positions) := by gcongr
           _ = _ := by dsimp [C]; ring
    have he : C*X.positions*l ≤ branchAccesses X Y c C 1 n := by
      unfold branchAccesses
      apply le_trans _ (Nat.le_add_right _ _)
      rw [pow_one]
      exact (Nat.mul_assoc C X.positions l).le.trans
        (Nat.mul_le_mul_left C (Nat.le_add_right _ _))
    exact (Nat.cast_le.mpr (hcost.trans he)).trans_lt (hbudget labels hD hT A f hf z).1

end PairSimulation.TraversalRoles

end VPVNP
end Computability
end OAI
