import OAI.Computability.BorderVNP.CubeScatterRawPacket
import OAI.Computability.BorderVNP.CubeISAOwnedPacketStage
import OAI.Computability.BorderVNP.CubeScatterRawPrefixChunks
import OAI.Computability.BorderVNP.RoutingISALoops
import OAI.Computability.BorderVNP.RoutingISACallInversion

/-! # Recovering every copied selector chunk from a returning native packet scan

The induction follows the actual cursor and all its valid and skipped trials.
The shared selector prefix and all previously decoded physical packet cells
survive later writes to disjoint packet rectangles. No crossing input appears
in this induction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Scatter Physical Physical.Owned Cube.Tally VPVNP.BurstRAM DiagonalResidueRAM Owned OwnedVertex
open CellDispatch Physical.VertexIndex

variable {w n d blocks b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem foreign_slot (p q : Packet n d blocks) (ne : p ≠ q) (base : ℕ)
    (j : Fin (selectorWidth n K h)) :
    let stride := bankWidth n b h K s
    let x := bankAt base stride p+j.val
    x < bankAt base stride q ∨ bankAt base stride q+stride ≤ x := by
  intro stride x
  have width : selectorWidth n K h ≤ stride := by dsimp [stride,bankWidth,supplyBase]; omega
  have diff := (fun he => ne (packetIndex_injective he) : packetIndex p ≠ packetIndex q)
  rcases lt_or_gt_of_ne diff with lo | hi
  · have step := Nat.mul_le_mul_right stride lo
    rw [Nat.succ_mul] at step
    exact .inl (by dsimp only [x,bankAt]; have := j.isLt; omega)
  · have step := Nat.mul_le_mul_right stride hi
    rw [Nat.succ_mul] at step
    exact .inr (by dsimp only [x,bankAt]; omega)

private def Seen (i : Fin (n+1)) (p : Symbols d) (base : ℕ) (chunks : Fin (packetTrials n d blocks) → List Bool)
    (k : ℕ) (m : Memory w) : Prop :=
  ∀ t : Fin (packetTrials n d blocks), ∀ ht : packetTrialValid t, t.val < k →
    ∃ u : Selector n K h, chunks t = selectorStream u ∧
      SelectorRead.Stored (readings m) (bankAt base (bankWidth n b h K s) (packetRowEquiv i p ⟨t,ht⟩).val) u

/-- A real returning local packet loop validates every selected raw prefix chunk,
places the same selector in its packet rectangle, and consumes the whole selector
prefix. All exterior source cells and outer low registers survive. -/
theorem rawPacketLoop_return (src : Set ℕ) (i : Fin (n+1)) (pair : Symbols d) (high : Bool)
    (base sel : ℕ) (chunks : Fin (packetTrials n d blocks) → List Bool) (orig : Bank w) (old : Memory w)
    (ready : packetReady (blocks := blocks) i pair (bankWidth n b h K s) base 0 (.ofWords orig old))
    (group : readings orig 3 = (if high then pair.val.2 else pair.val.1).val)
    (axis : readings orig 4 = i.val) (dim : readings orig 5 = n)
    (width : readings orig 8 = selectorWidth n K h) (count : readings orig 9 = Fintype.card (Selector n K h))
    (start : orig 36 = word w sel)
    (positive : 0 < bankWidth n b h K s) (keys : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    (room : base+(d*d)^(n+1)*2*blocks*bankWidth n b h K s ≤ 2^w)
    (source : ∀ p : Packet n d blocks, p.1.1 i = pair → ∀ x ∈ src,
      x < bankAt base (bankWidth n b h K s) p ∨ bankAt base (bankWidth n b h K s) p+bankWidth n b h K s ≤ x)
    (length : ∀ t, packetTrialValid t → (chunks t).length = selectorWidth n K h)
    (bits : ∀ t, packetTrialValid t → Resident src old
      (sel+selectedPrefix (blocks := blocks) i pair t.val*selectorWidth n K h) (chunks t))
    {es t mt} (path : Runs pub mac (rowLoop (packetCandidate n) (ownedPacket n b h K s)) orig old es t mt) :
    (∀ j : Reg, j.val < 24 → j ≠ 18 → t j = orig j) ∧
      t 36 = word w (sel+(2*blocks*(d.choose 2)^n)*selectorWidth n K h) ∧ (∀ x ∈ src, mt x = old x) ∧
      ∀ k : Fin (packetTrials n d blocks), ∀ hk : packetTrialValid k,
        ∃ u : Selector n K h, chunks k = selectorStream u ∧ SelectorRead.Stored (readings mt)
          (bankAt base (bankWidth n b h K s) (packetRowEquiv i pair ⟨k,hk⟩).val) u := by
  let N := packetTrials n d blocks
  let stride := bankWidth n b h K s
  let offset (k : ℕ) := sel+selectedPrefix (blocks := blocks) i pair k*selectorWidth n K h
  let I (r : Bank w) (m : Memory w) := readings r 18 ≤ N ∧
    (∀ j : Reg, j.val < 24 → j ≠ 18 → r j = orig j) ∧ r 36 = word w (offset (readings r 18)) ∧
    (∀ x ∈ src, m x = old x) ∧ Seen (b := b) (h := h) (K := K) (s := s) i pair base chunks (readings r 18) m
  let body := Code.seq (packetCandidate n) (.seq (.ifEq 40 1 (ownedPacket n b h K s) .nop) (.binary .add 18 18 1))
  obtain ⟨r0,r1,r2,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19⟩ := ready
  have cap : N < 2^w := r19.symm.le.trans_lt (orig 19).isLt
  have step {r : Bank w} {m : Memory w} {gs z mz} (inv : I r m) (lt : r 18 < r 19)
      (run : Runs pub mac body r m gs z mz) : I z mz := by
    obtain ⟨_,persistent,selector,oldWords,seen⟩ := inv
    have low (j : Reg) (hj : j.val < 24) (hn : j ≠ 18) := congrArg Fin.val (persistent j hj hn)
    have bound : readings r 19 = N := (low _ (by decide) (by decide)).trans r19
    let k : Fin N := ⟨readings r 18,bound ▸ lt⟩
    let dest := base+trialPacketIndex d ((d*d)^i.val) blocks pair.val.1.val pair.val.2.val k.val*stride
    have space : dest+stride ≤ 2^w := by
      have hb := Nat.mul_le_mul_right stride (trialPacketIndex_lt i pair k)
      rw [Nat.succ_mul] at hb
      dsimp only [dest]
      change base+(d*d)^(n+1)*2*blocks*stride ≤ 2^w at room
      omega
    obtain ⟨_,v,mv,_,_,candidate,tail⟩ := seq_split run
    obtain ⟨_,y,my,_,_,branch,inc⟩ := seq_split tail
    have tested := (packetCandidate_run pub mac r m i pair k
      ((low _ (by decide) (by decide)).trans r0) ((low _ (by decide) (by decide)).trans r1)
      ((low _ (by decide) (by decide)).trans r2) ((low _ (by decide) (by decide)).trans r10)
      ((low _ (by decide) (by decide)).trans r11) ((low _ (by decide) (by decide)).trans r12)
      ((low _ (by decide) (by decide)).trans r13) ((low _ (by decide) (by decide)).trans r14)
      ((low _ (by decide) (by decide)).trans r15) ((low _ (by decide) (by decide)).trans r16)
      ((low _ (by decide) (by decide)).trans r17) rfl positive ((Nat.lt_add_of_pos_right positive).trans_le space)).asTest
        (packetCandidate_deterministic n)
    obtain ⟨addr,ori,_,flag,hold,same⟩ := (tested.sound candidate).2
    have keepV (j : Reg) (hj : j.val < 24) (hn : j ≠ 18) := (Fin.ext (hold j hj)).trans (persistent j hj hn)
    have srcV x hx := (Fin.ext (congrFun same x)).trans (oldWords x hx)
    have vsel := (candidate.keepsReg (packetCandidate_frame n).2.1).trans selector
    have unit : readings v 1 = 1 := (congrArg Fin.val (keepV _ (by decide) (by decide))).trans r1
    have eqFlag : v 40 = v 1 ↔ packetTrialValid k := by
      rw [Fin.ext_iff]
      change readings v 40 = readings v 1 ↔ _
      have fl : readings v 40 = if packetTrialValid k then 1 else 0 := flag
      by_cases ok : packetTrialValid k <;> simp [fl,unit,ok]
    have bump : Runs pub mac (.binary .add 18 18 1) y my [tick w] (bumpBank y 18) my := Runs.localStep _ rfl rfl
    obtain ⟨_,hz,hmz⟩ := inc.unique_of_deterministic (by decide) bump
    subst z
    subst mz
    obtain ⟨_,_,chosen⟩ := eq_split branch
    have advance (keep : ∀ j : Reg, j.val < 24 → y j = v j) :
        readings (bumpBank y 18) 18 = k.val+1 ∧
        ∀ j : Reg, j.val < 24 → j ≠ 18 → bumpBank y 18 j = orig j := by
      have h18 : readings y 18 = k.val := (congrArg Fin.val (keep 18 (by decide))).trans (hold 18 (by decide))
      have h1 : readings y 1 = 1 := (congrArg Fin.val (keep 1 (by decide))).trans unit
      refine ⟨?_,fun j hj hn => (Function.update_of_ne hn ..).trans ((keep j hj).trans (keepV j hj hn))⟩
      change ((bumpBank y 18) 18).val = k.val+1
      simp only [bumpBank,Function.update_self,Fin.val_add]
      change (y 18).val = k.val at h18
      change (y 1).val = 1 at h1
      rw [h18,h1,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt k.isLt cap)]
    by_cases ok : packetTrialValid k
    · rw [ite_eq_left (eqFlag.mpr ok)] at chosen
      let p := (packetRowEquiv i pair ⟨k,ok⟩).val
      have pr : p.1.1 i = pair := (packetRowEquiv i pair ⟨k,ok⟩).property
      have position : dest = bankAt base stride p := by dsimp only [dest,bankAt,p]; rw [trialPacketIndex_eq i pair ⟨k,ok⟩]
      have owner : OwnerInput (K := K) (h := h) p i high v := by
        refine ⟨pr ▸ (congrArg Fin.val (keepV 15 (by decide) (by decide))).trans r15,?_,?_,
          (congrArg Fin.val (keepV 4 (by decide) (by decide))).trans axis,
          (congrArg Fin.val (keepV 5 (by decide) (by decide))).trans dim,
          (congrArg Fin.val (keepV 8 (by decide) (by decide))).trans width,
          (congrArg Fin.val (keepV 9 (by decide) (by decide))).trans count⟩
        · exact ori.trans (selected_fields i pair k ok).2.2.1.symm
        · rw [groupSymbol,pr]
          exact (congrArg Fin.val (keepV 3 (by decide) (by decide))).trans group
      have wfit : selectorWidth n K h ≤ stride := by dsimp [stride,bankWidth,supplyBase]; omega
      obtain ⟨u,spelling,stored,next,keep,away⟩ := rawPacket_return src p i high (chunks k) (length k ok)
        (offset k.val) (bankAt base stride p) v mv owner vsel (position ▸ addr) keys (position ▸ space)
        ((bits k ok).congr srcV) (fun j hj he => by
          have side := source p pr _ he
          rw [length k ok] at hj
          change _ < bankAt base stride p ∨ bankAt base stride p+stride ≤ _ at side
          omega) chosen
      obtain ⟨adv,persist⟩ := advance (fun j hj => keep j (by omega))
      refine ⟨adv ▸ k.isLt,persist,?_,fun x hx => (away x (source p pr x hx)).trans (srcV x hx),?_⟩
      · change y 36 = word w (offset (readings (bumpBank y 18) 18))
        rw [adv]
        simpa only [offset,selectedPrefix_next,ite_eq_left ok,Nat.succ_mul,Nat.add_assoc] using next
      · intro a ha prev
        change a.val < readings (bumpBank y 18) 18 at prev
        rw [adv] at prev
        by_cases eqn : a=k
        · subst a; exact ⟨u,spelling,stored⟩
        have lt : a.val < k.val := by have := (Fin.val_ne_of_ne eqn); omega
        obtain ⟨prior,word,held⟩ := seen a ha lt
        refine ⟨prior,word,fun j => ?_⟩
        let a' := (packetRowEquiv i pair ⟨a,ha⟩).val
        have diff : a' ≠ p := fun eqn' => eqn (congrArg Subtype.val ((packetRowEquiv i pair).injective (Subtype.ext eqn')))
        exact (congrArg Fin.val (away _ (foreign_slot a' p diff base j))).trans ((congrFun same _).trans (held j))
    · rw [ite_eq_right (eqFlag.not.mpr ok)] at chosen
      have nop : Runs pub mac .nop v mv [tick w] v mv := Runs.localStep _ rfl rfl
      obtain ⟨_,eqR,eqM⟩ := chosen.unique_of_deterministic (by decide) nop
      subst y
      subst my
      obtain ⟨adv,persist⟩ := advance (fun _ _ => rfl)
      refine ⟨adv ▸ k.isLt,persist,?_,srcV,?_⟩
      · change v 36 = word w (offset (readings (bumpBank v 18) 18))
        rw [adv]
        simpa only [offset,selectedPrefix_next,ite_eq_right ok,Nat.add_zero] using vsel
      · intro a ha prev
        change a.val < readings (bumpBank v 18) 18 at prev
        rw [adv] at prev
        have ne : a ≠ k := fun eqn => ok (eqn ▸ ha)
        have lt : a.val < k.val := by have := Fin.val_ne_of_ne ne; omega
        obtain ⟨prior,word,held⟩ := seen a ha lt
        exact ⟨prior,word,fun j => (congrFun same _).trans (held j)⟩
  have initial : I orig old := by
    refine ⟨by rw [show readings orig 18 = 0 from r18]; exact Nat.zero_le _,
      fun _ _ _ => rfl,?_,fun _ _ => rfl,?_⟩
    · simpa [offset,show readings orig 18 = 0 from r18,selectedPrefix] using start
    · intro k _ hk
      change k.val < readings orig 18 at hk
      rw [show readings orig 18 = 0 from r18] at hk
      exact (Nat.not_lt_zero _ hk).elim
  obtain ⟨result,done⟩ := path.while_invariant 18 19 body I step rfl initial
  obtain ⟨bound,keep,cursor,words,seen⟩ := result
  have end19 : (t 19).val = N := (congrArg Fin.val (keep 19 (by decide) (by decide))).trans r19
  have final : readings t 18 = N := bound.antisymm (end19.symm.le.trans (le_of_not_gt done))
  exact ⟨keep,by simpa only [offset,final,N,selectedPrefix_end] using cursor,words,fun k hk => seen k hk (final ▸ k.isLt)⟩

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
