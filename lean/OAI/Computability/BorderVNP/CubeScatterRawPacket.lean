import OAI.Computability.BorderVNP.CubeScatterRawCopy
import OAI.Computability.BorderVNP.CubeScatterRawFrame

/-! # A returning packet validates its raw selector independently of the crossing data -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA RoutingISA.OwnedVertex Physical Physical.VertexIndex VPVNP.BurstRAM DiagonalResidueRAM Tally

variable {w n d blocks b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem body_noSelector (u : Selector n K h) (i : Fin (n+1)) (owner : Bool) :
    Mode.selector ∉ bodyModes b s u i owner := by
  intro member
  obtain ⟨pos,mem,eqn⟩ := List.mem_map.mp member
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp mem
  change (ownedPosition u i owner (fun _ _ => false) (fun _ _ => false) ((bodyOrder n b h s).symm k)).digit.mode = .selector at eqn
  generalize hc : (bodyOrder n b h s).symm k = slot at eqn
  cases slot with
  | inl q => rcases q with ⟨e,j⟩; simp only [ownedPosition] at eqn; split_ifs at eqn <;> cases eqn
  | inr q => rcases q with ⟨e,j⟩; simp only [ownedPosition] at eqn; split_ifs at eqn <;> cases eqn

private theorem decodeOwner_valid (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (r : Bank w) (m : Memory w) (base : ℕ) (owner : OwnerInput (K := K) (h := h) p i high r)
    (addr : readings r 24 = base) (two : 2 < 2^w) (room : base+selectorWidth n K h ≤ 2^w)
    {es t mt} (run : Runs pub mac decodeOwner r m es t mt) :
    SelectorRead.Valid (readings m) base (selectorWidth n K h) (Fintype.card (Selector n K h)) := by
  obtain ⟨y,my,_,_,_,setup,rest⟩ := Runs.seq_iff.mp run
  obtain ⟨_,_,_,_,_,read,_⟩ := Runs.seq_iff.mp rest
  have prim := effect_runs pub mac false r m selectorShape (by decide)
  obtain ⟨_,eqR,eqM⟩ := setup.unique_of_deterministic (by decide) prim
  subst y
  subst my
  have count : Fintype.card (Selector n K h) ≤ 2^w := owner.count.symm.le.trans (r 9).isLt.le
  have fit := Nat.clog_le_of_le_pow count
  let first := effect false r m selectorShape
  have p24 : readings first.bank 24 = base := addr
  have p41 : readings first.bank 41 = selectorWidth n K h := owner.bits
  have p42 : readings first.bank 42 = Fintype.card (Selector n K h) := owner.count
  exact ((SelectorRead.reader_run first.bank m base _ _ p24 p41 p42 two fit room).sound read).1

/-- Every return of the complete packet callback accepts the actual raw
selector chunk, advances exactly that selector cursor, and stores the recovered
selector rank. The body may copy arbitrary words from any crossing pointer. -/
theorem rawPacket_return (src : Set ℕ) (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (bs : List Bool) (len : bs.length = selectorWidth n K h) (sel base : ℕ)
    (r : Bank w) (m : Memory w) (owner : OwnerInput (K := K) (h := h) p i high r)
    (rsel : r 36 = word w sel) (addr : readings r 24 = base)
    (keys : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    (room : base+bankWidth n b h K s ≤ 2^w) (input : Resident src m sel bs)
    (off : ∀ j < bs.length, base+j ∉ src) {es t mt}
    (run : Runs pub mac (ownedPacket n b h K s) r m es t mt) :
    ∃ u : Selector n K h, bs = selectorStream u ∧ SelectorRead.Stored (readings mt) base u ∧
      t 36 = word w (sel+selectorWidth n K h) ∧ (∀ j : Reg, j.val < 36 → t j = r j) ∧
      ∀ x, x < base ∨ base+bankWidth n b h K s ≤ x → mt x = m x := by
  have span : selectorWidth n K h+bodyWidth n b h s = bankWidth n b h K s := by
    simp only [bodyWidth,bankWidth,supplyBase,Nat.add_assoc]
  have prefixRoom : base+selectorWidth n K h ≤ 2^w := by omega
  have one := (Nat.one_le_pow (n+1) 2 (by decide)).trans_lt ((le_max_right ..).trans_lt keys)
  have two : 2 < 2^w := (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ n+1)).trans_lt
    ((le_max_right ..).trans_lt keys)
  let c : Cursor := ⟨sel,(r 37).val,base⟩
  obtain ⟨a,fs,copied,hcursor,low⟩ := rawCopy_run (pub := pub) (mac := mac) src c bs len r m rsel
    (Fin.ext (word_val _ _ (r 37).isLt).symm)
    (Fin.ext (addr.trans (word_val _ _ (addr ▸ (r 24).isLt)).symm))
    input (fun j hj => ⟨off j hj,by change base+j < _; omega⟩)
  let img := rawImage bs base m
  obtain ⟨y,my,_,_,_,head,tail⟩ := Runs.seq_iff.mp run
  obtain ⟨v,mv,_,_,_,copy,decode⟩ := Runs.seq_iff.mp head
  have det : (copySelectors n K h).deterministic = true := (Bool.and_eq_true_iff.mp ownedPrefix_deterministic).1
  obtain ⟨_,eqR,eqM⟩ := copy.unique_of_deterministic det copied
  subst v
  subst mv
  have stable (j : Reg) (hj : j.val < 36) : a j = r j :=
    low j ((by decide : ∀ j : Reg, j.val < 36 → j ∉ ([36,37,38,59,60] : List Reg)) j hj)
  have en : OwnerInput (K := K) (h := h) p i high a := by
    obtain ⟨hu,ho,hg,hi,hn,hb,hk⟩ := owner
    constructor <;> apply Eq.trans (congrArg Fin.val (stable _ (by decide))) <;> assumption
  have a24 := (congrArg Fin.val (stable 24 (by decide))).trans addr
  have valid := decodeOwner_valid p i high a img base en a24 two prefixRoom decode
  obtain ⟨u,spelled,stored⟩ := rawImage_selector len one valid
  obtain ⟨z,gs,canonical,_,_,key,place,side,keep⟩ := decodeOwner_run (pub := pub) (mac := mac)
    p i high u a img base en a24 stored keys prefixRoom
  obtain ⟨_,eqR,eqM⟩ := decode.unique_of_deterministic (by decide) canonical
  subst y
  subst my
  have preserved (j : Reg) (hj : j.val < 39 ∨ j=59) :=
    keep j ((by decide : ∀ j : Reg, j.val < 39 ∨ j=59 → j ∉ decodeScratch) j hj)
  have d1 := (preserved 59 (by decide)).trans hcursor.2.2.2
  obtain ⟨ds,modes,_,endReg,endMem⟩ := (scatterPacket_iff u i (ownerBit i p.1.2 high) z img d1 key place side keys).mp tail
  let init := Function.update z (58 : Reg) 0
  have count : ds.length = bodyWidth n b h s := by
    simpa only [bodyModes,bodyPositions,List.length_map,List.length_ofFn] using congrArg List.length modes
  have frame := result_frame ds init img (base+bs.length) d1
    ((preserved 38 (by decide)).trans hcursor.2.2.1) (by omega)
  have none := modes ▸ body_noSelector (b := b) (s := s) u i (ownerBit i p.1.2 high)
  refine ⟨u,spelled,?_,?_,?_,?_⟩
  · intro j
    have hbefore : base+j.val < base+bs.length := by rw [len]; exact Nat.add_lt_add_left j.isLt _
    exact (congrArg Fin.val ((congrFun endMem _).trans (frame.2.2.1 _ (.inl hbefore)))).trans (stored j)
  · rw [endReg,frame.2.2.2 none]
    exact len ▸ (preserved 36 (by decide)).trans hcursor.1
  · intro j hj
    have held := (by decide : ∀ j : Reg, j.val < 36 → j ∉ ([36,37,38,60] : List Reg) ∧ j ≠ 58) j hj
    exact (congrFun endReg j).trans ((frame.2.1 j held.1).trans
      ((Function.update_of_ne held.2 ..).trans ((preserved j (.inl (by omega))).trans (stable j hj))))
  · intro x hx
    apply (congrFun endMem x).trans
    apply (frame.2.2.1 x (by omega)).trans
    apply image_outside
    rw [List.length_map]
    omega

end Cube.Scatter

end BorderVNP
end Computability
end OAI
