import OAI.ThreeFlat.RAM.TickLinkAddresses

namespace OAI
/-! # The three link arrays after each prefix of the actual native loops -/

namespace ThreeFlat.RAM.TickLinkRows

open Computability.VPVNP.BurstRAM PrivateRAM Collapse.TickLinkScan
open scoped Fin.CommRing
variable {w : ℕ} (P : Plan) (source : ℕ → ℕ)

def Loaded (m : Memory w) := ∀ i < P.sockets, m (P.slot i) = (source i : Word w)

/-- The socket prefix has consumed `i` trunks and the tail prefix has consumed
one remaining trunk for each source strictly below `tails`. -/
structure Correct (start m : Memory w) (i tails : ℕ) : Prop where
  lastAt : ∀ s < P.sources, m (P.lastBase+s) = (last P.sources source i s : Word w)
  prevAt : ∀ j < i, m (P.prevBase+j) = (prev P.sources source j : Word w)
  middleAt : ∀ j < i, m (P.dstBase+prev P.sources source j) = (middleSite P.cells P.sources j : Word w)
  tailAt : ∀ s < tails, m (P.dstBase+last P.sources source i s) =
    (tailSite P.cells P.sources P.sockets s : Word w)
  outside : ∀ a, ¬P.written a → m a = start a

private theorem init_prefix (fit : P.Fits w) (m : Memory w) (n : ℕ) (hn : n ≤ P.sources) (a : ℕ) :
    image .init P m n a =
      if P.lastBase ≤ a ∧ a < P.lastBase+n then ((a-P.lastBase : ℕ) : Word w) else m a := by
  induction n with
  | zero => simp [image]
  | succ n ih =>
    rw [image,action_init P fit _ (by omega : n < P.sources),putNat,ih (by omega)]
    split_ifs <;> first | rfl | (congr 1; omega)

private theorem init_correct (fit : P.Fits w) (start : Memory w) :
    Correct P source start (image .init P start P.sources) 0 0 := by
  refine ⟨?_,fun _ h => (Nat.not_lt_zero _ h).elim,fun _ h => (Nat.not_lt_zero _ h).elim,
    fun _ h => (Nat.not_lt_zero _ h).elim,?_⟩
  · intro s hs
    rw [init_prefix P fit start _ le_rfl,ite_eq_left (by omega : P.lastBase ≤ P.lastBase+s ∧
      P.lastBase+s < P.lastBase+P.sources),last_zero]
    simp
  · intro a away
    rw [init_prefix P fit start _ le_rfl]
    exact ite_eq_right (fun h => away (Or.inl h))

private theorem socket_correct (fit : P.Fits w) (bound : ∀ i < P.sockets, source i < P.sources)
    {start m : Memory w} (loaded : Loaded P source start) {i : ℕ}
    (hi : i < P.sockets) (h : Correct P source start m i 0) :
    Correct P source start (action .socket (P.data w) (i : Word w) m) (i+1) 0 := by
  have lfit := fit.last
  have pfit := fit.prev
  have sfit := bound i hi
  have ofit := prev_lt P.sources source sfit
  have raw := (h.outside _ (P.slot_unwritten fit hi)).trans (loaded i hi)
  rw [action_socket P fit m hi sfit (by omega : prev P.sources source i < P.sources+P.sockets) raw
    (h.lastAt _ sfit)]
  constructor
  · intro s hs
    by_cases hit : source i = s
    · subst s
      simp [putNat,last_succ]
    · simp only [putNat, ite_eq_right (show P.lastBase+s ≠ P.lastBase+source i by omega),
        ite_eq_right (show P.lastBase+s ≠ P.dstBase+prev P.sources source i by omega),
        ite_eq_right (show P.lastBase+s ≠ P.prevBase+i by omega), last_succ, ite_eq_right hit, h.lastAt s hs]
  · intro j hj
    simp only [putNat, ite_eq_right (show P.prevBase+j ≠ P.lastBase+source i by omega),
      ite_eq_right (show P.prevBase+j ≠ P.dstBase+prev P.sources source i by omega)]
    by_cases hit : j=i
    · subst j
      simp
    · rw [ite_eq_right (by omega),h.prevAt j (by omega)]
  · intro j hj
    simp only [putNat, ite_eq_right (show P.dstBase+prev P.sources source j ≠ P.lastBase+source i by omega)]
    by_cases hit : j=i
    · subst j
      simp
    · have lt : j < i := by omega
      have ne := prev_ne_prev P.sources source (bound j (lt.trans hi)) sfit lt
      rw [ite_eq_right (by omega), ite_eq_right (by omega : P.dstBase+prev P.sources source j ≠ P.prevBase+i),
        h.middleAt j lt]
  · intro s hs
    omega
  · intro a ha
    change ¬ ((_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _)) at ha
    simp only [putNat, ite_eq_right (by omega : a ≠ P.lastBase+source i),
      ite_eq_right (by omega : a ≠ P.dstBase+prev P.sources source i),ite_eq_right (by omega : a ≠ P.prevBase+i),
      h.outside a ha]

private theorem tail_correct (fit : P.Fits w) (bound : ∀ i < P.sockets, source i < P.sources)
    {start m : Memory w} {s : ℕ} (hs : s < P.sources) (h : Correct P source start m P.sockets s) :
    Correct P source start (action .tail (P.data w) (s : Word w) m) P.sockets (s+1) := by
  have lfit := fit.last
  have pfit := fit.prev
  have old := last_lt P.sources source hs P.sockets
  rw [action_tail P fit m hs old (h.lastAt s hs)]
  constructor
  · intro t ht
    rw [putNat,ite_eq_right (by omega),h.lastAt t ht]
  · intro j hj
    rw [putNat,ite_eq_right (by omega),h.prevAt j hj]
  · intro j hj
    have ne := prev_ne_last P.sources source (bound j hj) hs hj
    rw [putNat,ite_eq_right (by omega),h.middleAt j hj]
  · intro t ht
    by_cases hit : t=s
    · subst t
      simp [putNat]
    · have ne : last P.sources source P.sockets t ≠ last P.sources source P.sockets s :=
        fun eqn => hit (last_injective P.sources source P.sockets (by omega) hs eqn)
      rw [putNat,ite_eq_right (by omega),h.tailAt t (by omega)]
  · intro a ha
    change ¬ ((_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _)) at ha
    rw [putNat,ite_eq_right (by omega),h.outside a ha]

/-- A constant-program-size native builder with the full memory postcondition. -/
theorem output_correct (fit : P.Fits w) (bound : ∀ i < P.sockets, source i < P.sources)
    (start : Memory w) (loaded : Loaded P source start) :
    Correct P source start (output P start) P.sockets P.sources := by
  let init := image .init P start P.sources
  have scan (i : ℕ) (hi : i ≤ P.sockets) : Correct P source start (image .socket P init i) i 0 := by
    induction i with
    | zero => exact init_correct P source fit start
    | succ i ih => exact socket_correct P source fit bound loaded (by omega) (ih (by omega))
  have finish (s : ℕ) (hs : s ≤ P.sources) :
      Correct P source start (image .tail P (image .socket P init P.sockets) s) P.sockets s := by
    induction s with
    | zero => exact scan P.sockets le_rfl
    | succ s ih => exact tail_correct P source fit bound (by omega) (ih (by omega))
  exact finish P.sources le_rfl

theorem builder_correct (fit : P.Fits w) (bound : ∀ i < P.sockets, source i < P.sources) :
    (builder w P).Spec (Loaded P source)
      (fun m out => Correct P source m out P.sockets P.sources) (9+17*P.sources+26*P.sockets) := by
  have result (m : Memory w) (ok : Loaded P source m) := output_correct P source fit bound m ok
  intro pcs regs slots M pc reg pub exit installed data c m begin_ ok
  obtain ⟨t,ht,out,mem,run,done,rfl⟩ := builder_spec P
    (by have := fit.dst; omega : P.sources < 2^w) (by have := fit.dst; omega : P.sockets < 2^w)
    M pc reg pub exit installed data c m begin_ trivial
  exact ⟨t,ht,out,_,run,done,result m ok⟩

/-- The payloads read back as natural numbers in the numbered trivalent graph. -/
theorem Correct.final_values {m out : Memory w} (h : Correct P source m out P.sockets P.sources)
    (fit : P.Fits w) (bounded : ∀ i < P.sockets, source i < P.sources) :
    (∀ s < P.sources, (out (P.lastBase+s)).val = last P.sources source P.sockets s) ∧
    (∀ i < P.sockets, (out (P.prevBase+i)).val = prev P.sources source i) ∧
    (∀ i < P.sockets, (out (P.dstBase+prev P.sources source i)).val = middleSite P.cells P.sources i) ∧
    (∀ s < P.sources, (out (P.dstBase+last P.sources source P.sockets s)).val =
      tailSite P.cells P.sources P.sockets s) := by
  have edges := fit.dst
  have sites := fit.sites
  refine ⟨?_,?_,?_,?_⟩
  · intro s hs
    rw [h.lastAt s hs]
    exact Fin.val_cast_of_lt ((last_lt P.sources source hs P.sockets).trans_le (by omega))
  · intro i hi
    rw [h.prevAt i hi]
    exact Fin.val_cast_of_lt ((prev_lt P.sources source (bounded i hi)).trans_le (by omega))
  · intro i hi
    rw [h.middleAt i hi]
    exact Fin.val_cast_of_lt (by unfold middleSite; omega)
  · intro s hs
    rw [h.tailAt s hs]
    exact Fin.val_cast_of_lt (by unfold tailSite; omega)

theorem time_le_linear (p hidden : ℕ) (s : P.sources = 2+p+hidden) :
    9+17*P.sources+26*P.sockets ≤ 78*(1+P.cells+p+hidden) := by
  unfold Plan.sockets
  omega

end ThreeFlat.RAM.TickLinkRows

end OAI
