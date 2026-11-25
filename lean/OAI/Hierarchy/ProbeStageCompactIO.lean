import OAI.Hierarchy.ProbeStageCompactIOBase

namespace OAI
/-! # Native gather and writeback at the current tile ordinal -/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ}

private def incoming (h d : ℕ) (j : Fin (rounds d)) (k : ℕ) :=
  srcBase (h:=h) j (Fin.ofNat 6 k)

private def gatherPrefix {w : ℕ} (b : ℕ) (src : ℕ → ℕ) (i : ℕ) (m : Memory w) (n a : ℕ) :=
  if b≤ a ∧ a< b+n then m (src (a-b)+i) else m a

def staged (j : Fin (rounds d)) (i : Fin (2^h)) (m : Memory (ramWidth h d)) :=
  gatherPrefix (base h) (incoming h d j) i.val m 6

def stage (h d : ℕ) (j : Fin (rounds d)) : Procedure (ramWidth h d) :=
  countSeq (fun k=> WordStore.put _ (base h+k) (.load (pointer (base h) (incoming h d j k)))) 5

def stageClock := 108
def stageText := 186

theorem stage_text (h d : ℕ) (j : Fin (rounds d)) : text (stage h d j)=stageText :=
  countSeq_text _ 5 31 (fun _ _=> load_put_text _ _ _ _)

theorem stage_cheap (h d : ℕ) (j : Fin (rounds d)) : CheapCode (stage h d j) :=
  countSeq_cheap _ _ (fun _ _=> load_put_cheap _ _ _ _)

theorem staged_read (j : Fin (rounds d)) (i : Fin (2^h)) (m : Memory (ramWidth h d)) (q : Fin 6) :
    staged j i m (base h+q.val)=m (srcAddr j i q) := by
  have hi := q.isLt
  simp [staged,gatherPrefix,incoming,srcAddr,hi]

theorem staged_frame (j : Fin (rounds d)) (i : Fin (2^h)) (m : Memory (ramWidth h d)) (a : ℕ)
    (away : a< base h ∨ base h+6≤ a) : staged j i m a=m a := ite_eq_right (by omega)

theorem stage_exec (hd : 1≤ d) (large : 4≤ h) (j : Fin (rounds d)) (i : Fin (2^h))
    (m : Memory (ramWidth h d)) (cursor : m (base h+6)=(i.val:Word (ramWidth h d))) :
    (stage h d j).Exec m (staged j i m) stageClock := by
  let b:=base h
  let src:=incoming h d j
  let s:=gatherPrefix b src i.val m
  have empty : s 0=m := by funext a;exact ite_eq_right (by omega)
  suffices run : (stage h d j).Exec (s 0) (s 6) stageClock by rwa [empty] at run
  apply countSeq_exec _ s 18 5
  intro k small
  have room : b+8<2^ramWidth h d:=window_room hd large j i
  have bounds := source_facts hd large j i (Fin.ofNat 6 k)
  change b+8≤ src k+i.val ∧ src k+i.val<2^ramWidth h d at bounds
  have cur : s k (b+6)=(i.val:Word (ramWidth h d)) := (ite_eq_right (by omega)).trans cursor
  have value : WordStore.value (b+k) (.load (pointer b (src k))) (s k)=m (src k+i.val) := by
    change s k (WordStore.value (b+k) (pointer b (src k)) (s k)).val=_
    rw [pointer_value b (src k) (b+k) _ _ (by omega) cur,Fin.val_cast_of_lt bounds.2]
    exact ite_eq_right (by omega)
  have next : Function.update (s k) (b+k) (WordStore.value (b+k) (.load (pointer b (src k))) (s k))=s (k+1) := by
    rw [value]
    funext a
    by_cases eqn : a=b+k
    · subst a;simp [s,gatherPrefix]
    · rw [Function.update_of_ne eqn]
      simp only [s,gatherPrefix,show (b≤ a ∧ a< b+(k+1)) ↔ (b≤ a ∧ a< b+k) by omega]
  rw [←next]
  intro P R K M
  exact WordStore.execute (b+k) (.load (pointer b (src k))) (s k) (by omega) M

private def destination (h d : ℕ) (j : Fin (rounds d)) (k : ℕ) := bankBase h d copies j k
private def scatterProc (w b dst k : ℕ) :=
  (WordStore.put w b (pointer b dst)).seq (RankUpdate.store w b (b+3+k))

private def scattered {w : ℕ} (b : ℕ) (dst : ℕ→ℕ) (i : ℕ) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | k+1 =>
    let last:=scattered b dst i m k
    Function.update (Function.update last b ((dst k+i:ℕ):Word w)) (dst k+i) (last (b+3+k))

private def clearPrefix {w : ℕ} (b : ℕ) (m : Memory w) (n a : ℕ) : Word w :=
  if b≤ a ∧ a< b+n then 0 else m a

def unstaged (j : Fin (rounds d)) (i : Fin (2^h)) (m : Memory (ramWidth h d)) :=
  clearPrefix (base h) (scattered (base h) (destination h d j) i.val m 3) 6

def unstage (h d : ℕ) (j : Fin (rounds d)) : Procedure (ramWidth h d) :=
  (countSeq (fun k=> scatterProc (ramWidth h d) (base h) (destination h d j k) k) 2).seq
    (countSeq (fun k=> WordStore.put _ (base h+k) (.lit 0)) 5)

def unstageClock := 123
def unstageText := 198

theorem unstage_text (h d : ℕ) (j : Fin (rounds d)) : text (unstage h d j)=unstageText := by
  rw [unstage,text_seq,countSeq_text _ 2 36 (by
    intro k _
    rw [scatterProc,text_seq,pointer_put_text]; rfl),
    countSeq_text _ 5 15 (fun _ _=> zero_put_text _ _)]
  rfl

theorem unstage_cheap (h d : ℕ) (j : Fin (rounds d)) : CheapCode (unstage h d j) :=
  cheap_seq (countSeq_cheap _ _ (fun _ _=> cheap_seq (pointer_put_cheap _ _ _ _) (dynamic_cheap _ _ _)))
    (countSeq_cheap _ _ (fun _ _=> zero_put_cheap _ _))

private theorem scatter_frame {w : ℕ} (b : ℕ) (dst : ℕ→ℕ) (i : ℕ) (m : Memory w) (n a : ℕ)
    (control : a≠b) (away : ∀k< n,a≠dst k+i) : scattered b dst i m n a=m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scattered,Function.update_of_ne (away n (by omega)),Function.update_of_ne control]
    exact ih (fun k hk=> away k (by omega))

theorem unstaged_zero (j : Fin (rounds d)) (i : Fin (2^h)) (m : Memory (ramWidth h d)) (q : Fin 6) :
    unstaged j i m (base h+q.val)=0 := ite_eq_left (by have := q.isLt;omega)

theorem unstaged_frame (j : Fin (rounds d)) (i : Fin (2^h)) (m : Memory (ramWidth h d)) (a : ℕ)
    (window : a< base h ∨ base h+6≤ a) (rank : ∀ q : Fin 3,a≠rankAddr h d j q i) :
    unstaged j i m a=m a := by
  rw [unstaged,clearPrefix,ite_eq_right (by omega)]
  exact scatter_frame _ _ _ _ _ _ (by omega) (fun k hk=> rank ⟨k,hk⟩)

private theorem rank_distinct (j : Fin (rounds d)) (i : Fin (2^h)) {k q : Fin 3} (ne : k≠q) :
    rankAddr h d j k i ≠ rankAddr h d j q i := by
  intro eqn
  have same : (Cell.rank k i : Cell h d)=Cell.rank q i :=
    cell_injective h d j (show (Cell.rank k i : Cell h d).addr j=(Cell.rank q i).addr j from eqn)
  exact ne (Cell.rank.inj same).1

theorem unstaged_rank (_hd : 1≤ d) (large : 4≤ h) (j : Fin (rounds d)) (i : Fin (2^h))
    (m : Memory (ramWidth h d)) (q : Fin 3) :
    unstaged j i m (rankAddr h d j q i)=m (base h+3+q.val) := by
  let b:=base h
  let dst:=destination h d j
  have away (k : ℕ) (hk : k<3) : b+8≤ dst k+i.val := window_rank large j i ⟨k,hk⟩
  have hit (n : ℕ) (hn : n≤3) (hq : q.val< n) :
      scattered b dst i.val m n (dst q.val+i.val)=m (b+3+q.val) := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases same : q.val=n
      · rw [←same,scattered,Function.update_self]
        exact scatter_frame _ _ _ _ _ _ (by omega) (fun k hk=> by
          have := away k (by omega)
          have := q.isLt
          omega)
      · have ne : dst q.val+i.val≠dst n+i.val := rank_distinct j i (q:=⟨n,by omega⟩) (by
          intro eqn;exact same (congrArg Fin.val eqn))
        have outside:=away q.val q.isLt
        rw [scattered,Function.update_of_ne ne,Function.update_of_ne (by omega : dst q.val+i.val≠b)]
        exact ih (by omega) (by omega)
  have bound:=window_rank large j i q
  rw [unstaged,clearPrefix,ite_eq_right (by omega)]
  exact hit 3 le_rfl q.isLt

theorem unstage_exec (hd : 1≤ d) (large : 4≤ h) (j : Fin (rounds d)) (i : Fin (2^h))
    (m : Memory (ramWidth h d)) (cursor : m (base h+6)=(i.val:Word (ramWidth h d))) :
    (unstage h d j).Exec m (unstaged j i m) unstageClock := by
  let b:=base h
  let dst:=destination h d j
  let s:=scattered b dst i.val m
  have room : b+8<2^ramWidth h d:=window_room hd large j i
  have away (k : ℕ) (hk : k<3) : b+8≤ dst k+i.val := window_rank large j i ⟨k,hk⟩
  have copy : (countSeq (fun k=> scatterProc _ b (dst k) k) 2).Exec m (s 3) (3*21) := by
    apply countSeq_exec _ s 21 2
    intro k hk
    have cur : s k (b+6)=(i.val:Word (ramWidth h d)) :=
      (scatter_frame _ _ _ _ _ _ (by omega) (fun z hz=> by have := away z (by omega);omega)).trans cursor
    have p := pointer_value b (dst k) b _ _ (by omega) cur
    let mid:=Function.update (s k) b ((dst k+i.val:ℕ):Word (ramWidth h d))
    have put : (WordStore.put _ b (pointer b (dst k))).Exec (s k) mid 16 := by
      dsimp only [mid]
      rw [←p]
      exact WordStore.execute b (pointer b (dst k)) (s k) (by omega)
    have fits : dst k+i.val<2^ramWidth h d := by have := rank_room hd j ⟨k,by omega⟩ i;exact Nat.lt_of_succ_lt this
    have result : RankUpdate.stored b (b+3+k) mid=s (k+1) := by
      change writeMemory mid (mid (b:Word (ramWidth h d)).val) (mid ((b+3+k:ℕ):Word (ramWidth h d)).val)=_
      rw [Fin.val_cast_of_lt (by omega : b<2^ramWidth h d),
        Fin.val_cast_of_lt (by omega : b+3+k<2^ramWidth h d)]
      simp only [mid,Function.update_self,Function.update_of_ne (by omega : b+3+k≠b)]
      funext a
      simp only [writeMemory,Fin.val_cast_of_lt fits]
      simp [s,scattered,Function.update_apply]
    rw [←result]
    intro P R K M
    exact Procedure.Exec.then put (RankUpdate.store_exec b (b+3+k) mid) M
  let z:=clearPrefix b (s 3)
  have clear : (countSeq (fun k=> WordStore.put _ (b+k) (.lit 0)) 5).Exec (s 3) (z 6) (6*10) := by
    have empty : z 0=s 3 := by funext a;exact ite_eq_right (by omega)
    suffices run : (countSeq (fun k=> WordStore.put _ (b+k) (.lit 0)) 5).Exec (z 0) (z 6) (6*10) by
      rwa [empty] at run
    apply countSeq_exec _ z 10 5
    intro k hk
    have next : Function.update (z k) (b+k) (0:Word (ramWidth h d))=z (k+1) := by
      funext a
      by_cases eqn : a=b+k
      · subst a;simp [z,clearPrefix]
      · rw [Function.update_of_ne eqn]
        simp only [z,clearPrefix,show (b≤ a ∧ a< b+(k+1)) ↔ (b≤ a ∧ a< b+k) by omega]
    rw [←next]
    intro P R K M
    exact WordStore.execute (b+k) (.lit 0) (z k) (by omega) M
  intro P R K M
  exact Procedure.Exec.then copy clear M

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
