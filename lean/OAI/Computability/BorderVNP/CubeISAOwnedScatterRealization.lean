import OAI.Computability.BorderVNP.CubeISAOwnedScatterPacket

/-! # Recovering demand and supply words from a native scatter realization -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA Physical Physical.VertexIndex VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

variable {w n d blocks b h K s : ℕ}

/-- The body contains only private bits, crossing bits and unused reservations. -/
theorem body_selector_nil (u : Selector n K h) (i : Fin (n+1)) (owner : Bool)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    (bodyPositions u i owner x z).filterMap Position.selectorBit = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro p hp
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp
  cases (bodyOrder n b h s).symm k with
  | inl e => simp only [ownedPosition]; split_ifs <;> rfl
  | inr e => simp only [ownedPosition]; split_ifs <;> rfl

/-- The packet consumes its fixed selector prefix and exactly the declared crossing payload.
The destination reaches the end of its full reservation. -/
theorem ownedPacket_advance (u : Selector n K h) (i : Fin (n+1)) (owner : Bool) (c : Cursor)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    advance (bodyPositions u i owner x z) (advance (selectorPositions u) c) =
      ⟨c.selector + selectorWidth n K h,c.crossing + ∑ v : Vertex (n+1), payload (onEdge s) u.2 (v,i),
        c.dest + bankWidth n b h K s⟩ := by
  rw [selectors_advance,advance_counts,body_selector_nil,body_cross_length]
  simp [bodyPositions,bankWidth,supplyBase,bodyWidth,Nat.add_assoc]

/-- Erase the value of a locally chosen bit, retaining precisely the routed source requirements. -/
def Position.routed : Position → Position
  | .localBit _ => .unused
  | p => p

private theorem ready_routed {src : Set ℕ} {p q : Position} {c : Cursor} {m : Memory w}
    (eqn : p.routed = q.routed) : p.ready src c m ↔ q.ready src c m := by
  cases p <;> cases q <;> simp_all [Position.routed,Position.ready]

private theorem next_routed {p q : Position} {c : Cursor}
    (eqn : p.routed = q.routed) : c.next p = c.next q := by
  cases p <;> cases q <;> simp_all [Position.routed,Cursor.next]

/-- Altering the private choices does not change any routed input or destination address check. -/
theorem Prepared.of_routed {src : Set ℕ} {ps qs : List Position} {c : Cursor} {m : Memory w}
    (hp : Prepared src ps c m) (eqn : ps.map Position.routed = qs.map Position.routed) : Prepared src qs c m := by
  induction ps generalizing qs c with
  | nil =>
    obtain rfl : qs = [] := by simpa using eqn.symm
    trivial
  | cons p ps ih =>
    cases qs with
    | nil => simp at eqn
    | cons q qs =>
      obtain ⟨head,tail⟩ := List.cons.inj eqn
      exact ⟨(ready_routed head).mp hp.1,next_routed (c := c) head ▸ ih hp.2 tail⟩

/-- Recover a private bit when present, using the prior field value at routed or unused slots. -/
def Digit.merge (prior : Bool) : Digit → Bool
  | .privateBit bit => bit
  | _ => prior

private theorem localDigit {d : Digit} (prior : Bool) (hm : d.mode = .privateBit) :
    Position.digit (.localBit (d.merge prior)) = d := by
  cases d <;> simp_all [Digit.mode,Digit.merge,Position.digit]

private theorem merge_keep {d : Digit} (prior : Bool) (hm : d.mode ≠ .privateBit) :
    d.merge prior = prior := by cases d <;> simp_all [Digit.mode,Digit.merge]

private theorem same_digit {p : Position} {d : Digit} (hm : d.mode = p.digit.mode) (hn : d.mode ≠ .privateBit) :
    p.digit = d := by cases p <;> cases d <;> simp_all [Digit.mode,Position.digit]

/-- Every realizable digit list specifies actual demand and supply functions, extending prior
values on all non-owned demands, crossing supplies and non-owned internal supplies. -/
theorem bodyDigits_recover (u : Selector n K h) (i : Fin (n+1)) (owner : Bool) (ds : List Digit)
    (modes : ds.map Digit.mode = bodyModes b s u i owner)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    ∃ x' z', (bodyPositions u i owner x' z').map Position.digit = ds ∧
      (∀ e j, finTwoEquiv ((if e.2 then stop e.1 else start e.1) i) ≠ owner → x' e j = x e j) ∧
      (∀ e j, e.2 = i ∨ finTwoEquiv (e.1 i) ≠ owner → z' e j = z e j) ∧
      (bodyPositions u i owner x z).map Position.routed = (bodyPositions u i owner x' z').map Position.routed := by
  have known := bodyModes_eq u i owner x z
  have md := modes.trans known.symm
  have len : ds.length = bodyWidth n b h s := by simpa [bodyPositions] using congrArg List.length md
  let field (q : BodySlot n b h s) := ds[(bodyOrder n b h s q).val]'(by rw [len]; exact (bodyOrder n b h s q).isLt)
  have mode (q : BodySlot n b h s) : (field q).mode = (ownedPosition u i owner x z q).digit.mode := by
    have hit := List.ext_getElem_iff.mp md
    let k := bodyOrder n b h s q
    have h1 : k.val < (ds.map Digit.mode).length := by simpa only [List.length_map,len] using k.isLt
    have h2 : k.val < ((bodyPositions u i owner x z).map (fun p => p.digit.mode)).length := by
      simpa only [bodyPositions,List.length_map,List.length_ofFn] using k.isLt
    simpa [field,k,bodyPositions] using hit.2 k.val h1 h2
  let x' (e : Ends n) (j : Fin (h*b)) := (field (.inl (e,j))).merge (x e j)
  let pos (e : Edge (n+1)) (j : Fin (payload (onEdge s) u.2 e)) : Fin (h*s) :=
    ⟨j.val,j.isLt.trans_le (supplyWidth_le u e s)⟩
  let z' (e : Edge (n+1)) (j : Fin (payload (onEdge s) u.2 e)) := (field (.inr (e,pos e j))).merge (z e j)
  have xd (e : Ends n) (j : Fin (h*b)) (hn : finTwoEquiv ((if e.2 then stop e.1 else start e.1) i) ≠ owner) :
      x' e j = x e j := by
    apply merge_keep
    rw [mode]
    simp [ownedPosition,hn,Position.digit,Digit.mode]
  have zd (e : Edge (n+1)) (j : Fin (payload (onEdge s) u.2 e))
      (hn : e.2 = i ∨ finTwoEquiv (e.1 i) ≠ owner) : z' e j = z e j := by
    apply merge_keep
    rw [mode]
    rcases hn with h | h
    · simp [ownedPosition,pos,j.isLt,h,Position.digit,Digit.mode]
    · by_cases eqn : e.2 = i <;> simp [ownedPosition,pos,j.isLt,eqn,h,Position.digit,Digit.mode]
  have digit (q : BodySlot n b h s) : (ownedPosition u i owner x' z' q).digit = field q := by
    have hm := mode q
    cases q with
    | inl a =>
      rcases a with ⟨e,j⟩
      by_cases side : finTwoEquiv ((if e.2 then stop e.1 else start e.1) i) = owner
      · simp only [ownedPosition,side,ite_true,Position.digit,Digit.mode] at hm
        simpa only [ownedPosition,side,ite_true,x'] using localDigit (x e j) hm
      · simp only [ownedPosition,side,ite_false] at hm ⊢
        exact same_digit hm (by rw [hm]; decide)
    | inr a =>
      rcases a with ⟨e,j⟩
      by_cases hj : j.val < payload (onEdge s) u.2 e
      · simp only [ownedPosition,hj,dite_true] at hm ⊢
        by_cases hi : e.2 = i
        · simp only [hi,ite_true,zd e ⟨j.val,hj⟩ (Or.inl hi)] at hm ⊢
          exact same_digit hm (by rw [hm]; simp [Position.digit,Digit.mode])
        · simp only [hi,ite_false] at hm ⊢
          by_cases side : finTwoEquiv (e.1 i) = owner
          · simp only [side,ite_true,Position.digit,Digit.mode] at hm
            simpa only [side,ite_true,z',pos] using localDigit (z e ⟨j.val,hj⟩) hm
          · simp only [side,ite_false] at hm ⊢
            exact same_digit hm (by rw [hm]; decide)
      · simp only [ownedPosition,hj,dite_false] at hm ⊢
        exact same_digit hm (by rw [hm]; decide)
  refine ⟨x',z',?_,xd,zd,?_⟩
  · apply List.ext_getElem (by simp [bodyPositions,len])
    intro j hj _
    let k : Fin (bodyWidth n b h s) := ⟨j,by simpa [bodyPositions] using hj⟩
    simpa only [field,Equiv.apply_symm_apply,bodyPositions,List.getElem_map,List.getElem_ofFn] using
      digit ((bodyOrder n b h s).symm k)
  · simp only [bodyPositions,List.map_ofFn,Function.comp_def]
    congr 1
    funext k
    cases (bodyOrder n b h s).symm k with
    | inl q => simp only [ownedPosition]; split_ifs <;> rfl
    | inr q =>
      rcases q with ⟨e,j⟩
      by_cases hj : j.val < payload (onEdge s) u.2 e
      · by_cases hi : e.2 = i
        · simp [ownedPosition,hj,hi,zd e ⟨j.val,hj⟩ (.inl hi)]
        · simp only [ownedPosition,hj,dite_true,hi,ite_false]; split_ifs <;> rfl
      · simp [ownedPosition,hj]


variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- All returning packet traces from the same entry bank with the same local choices are identical. -/
theorem ownedPacket_unique {u : Selector n K h} {i : Fin (n+1)} {owner : Bool} {r a : Bank w}
    {m ma : Memory w} {pre} (preRun : Runs pub mac (ownedPrefix n K h) r m pre a ma)
    (one : a 59 = 1) (key : a 43 = word w (selectorOrder n K h u).val)
    (place : a 44 = word w (2^i.val)) (side : a 45 = wordBit w owner)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w) {es fs t t' mt mt'}
    (run : Runs pub mac (ownedPacket n b h K s) r m es t mt)
    (run' : Runs pub mac (ownedPacket n b h K s) r m fs t' mt')
    (eqn : es.flatMap TeamRAM.Event.choices = fs.flatMap TeamRAM.Event.choices) :
    es = fs ∧ t = t' ∧ mt = mt' := by
  obtain ⟨d₁,m₁,rfl,rfl,rfl⟩ := (ownedPacket_iff preRun one key place side fit).mp run
  obtain ⟨d₂,m₂,rfl,rfl,rfl⟩ := (ownedPacket_iff preRun one key place side fit).mp run'
  have h₁ := (result_trace d₁ (Function.update a (58 : Reg) 0) ma).1.2.1
  have h₂ := (result_trace d₂ (Function.update a (58 : Reg) 0) ma).1.2.1
  simp only [List.flatMap_append,List.append_cancel_left_eq,h₁,h₂] at eqn
  obtain rfl := choices_injective (m₁.trans m₂.symm) eqn
  exact ⟨rfl,rfl,rfl⟩

/-- Invert an arbitrary returning native packet into concrete physical demands and supplies.
The exact trace, memory, cursors, cost, positive signs and non-owned values are all retained. -/
theorem ownedPacket_recover (src : Set ℕ) (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (u : Selector n K h) (c : Cursor) (r : Bank w) (m : Memory w)
    (entry : OwnerInput (K := K) (h := h) p i high r) (sel : r 36 = word w c.selector)
    (cross : r 37 = word w c.crossing) (addr : readings r 24 = c.dest)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    (room : c.dest + selectorWidth n K h ≤ 2^w)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool)
    (input : Prepared src (selectorPositions u ++ bodyPositions u i (ownerBit i p.1.2 high) x z) c m)
    {es t mt} (run : Runs pub mac (ownedPacket n b h K s) r m es t mt) :
    ∃ x' z', let owner := ownerBit i p.1.2 high
             let ps := bodyPositions u i owner x' z'
             let mid := advance (selectorPositions u) c
             (∀ e j, finTwoEquiv ((if e.2 then stop e.1 else start e.1) i) ≠ owner → x' e j = x e j) ∧
             (∀ e j, e.2 = i ∨ finTwoEquiv (e.1 i) ≠ owner → z' e j = z e j) ∧
             TraceOK es ((ps.map Position.digit).flatMap Digit.choices) es.length ∧
             traceCost es ≤ ownedPacketCost n b h K s ∧ mt = image ps mid.dest (image (selectorPositions u) c.dest m) ∧
             (advance ps mid).loaded t ∧ ∀ j : Reg, j.val < 36 → t j = r j := by
  let owner := ownerBit i p.1.2 high
  obtain ⟨preIn,bodyIn⟩ := input.split
  obtain ⟨a,pre,preRun,preOK,_,loaded,key,place,side,_⟩ :=
    ownedPrefix_run (pub := pub) (mac := mac) src p i high u c r m entry sel cross addr fit room preIn
  obtain ⟨ds,modes,real,_,_⟩ := (ownedPacket_iff preRun loaded.2.2.2 key place side fit).mp run
  obtain ⟨x',z',digits,hx,hz,routed⟩ := bodyDigits_recover u i owner ds modes x z
  have bits : es.flatMap TeamRAM.Event.choices = ds.flatMap Digit.choices := by
    rw [real]
    simp only [List.flatMap_append,preOK.2.1,List.nil_append,(result_trace ds _ _).1.2.1]
    simp [tick]
  obtain ⟨t',fs,path,tr,cost,final,keep⟩ :=
    ownedPacket_run (pub := pub) (mac := mac) src p i high u c r m entry sel cross addr fit room preIn x' z'
      (bodyIn.of_routed routed)
  have eqn := ownedPacket_unique preRun loaded.2.2.2 key place side fit run path
    (bits.trans ((congrArg (List.flatMap Digit.choices) digits).symm.trans tr.2.1.symm))
  exact ⟨x',z',hx,hz,eqn.1 ▸ tr,eqn.1 ▸ cost,eqn.2.2,eqn.2.1 ▸ final,eqn.2.1 ▸ keep⟩

end Cube.Scatter

end BorderVNP
end Computability
end OAI
