import OAI.Hierarchy.DescentTerminalDenseHeaderRAM

namespace OAI
/-! # Numerical address headers in the concatenated order of genuine cable groups -/

namespace Hierarchy.DescentTerminalHeaderGroups
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalCableOrder DescentTerminalDenseWindow
open DescentTerminalDenseHeader DescentTerminalDenseCableFetch DescentTerminalDenseGraphRead
open ThreeFlat.Routing Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {q p n : ℕ}

def listMass (v : List (Profile q p)) := (v.map mass).sum

theorem prior_list (v : List (Profile q p)) (k : ℕ) (bound : k ≤ v.length) :
    priorBits v.get k=listMass (v.take k) := by
  induction k with
  | zero=>simp [priorBits,pref,listMass]
  | succ k ih=>
    let i : Fin v.length:=⟨k,by omega⟩
    rw [show priorBits v.get (k+1)=priorBits v.get k+mass (v.get i) from prior_next _ i,
      ih (by omega), List.take_succ_eq_append_getElem (l:=v) (i:=k) (by omega)]
    simp only [listMass, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton, List.get_eq_getElem, i]

theorem mass_append (a b : List (Profile q p)) : listMass (a++b)=listMass a+listMass b := by
  simp [listMass]

def chunkRows (len : Fin n→ℕ) (small : ∀i,len i ≤ p) (q : ℕ) : List (Profile q p) :=
  List.ofFn fun r : Fin (poolBatchCount n q)=>rowProfile len small r.val

@[simp] theorem chunkRows_length (len : Fin n→ℕ) (small : ∀i,len i ≤ p) :
    (chunkRows len small q).length=poolBatchCount n q := by simp [chunkRows]

theorem chunk_mass (len : Fin n→ℕ) (small : ∀i,len i ≤ p) (r : ℕ) (h : r ≤ poolBatchCount n q) :
    listMass ((chunkRows len small q).take r)=pref len (r*q) := by
  induction r with
  | zero=>simp [listMass,pref]
  | succ r ih=>
    have live : r<(chunkRows len small q).length := by simp;omega
    rw [List.take_succ_eq_append_getElem live,mass_append,ih (by omega),mass_row len small r]
    simp [listMass,chunkRows]

theorem pref_ended (len : Fin n→ℕ) (j : ℕ) (enough : n ≤ j) : pref len j=pref len n := by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le enough
  induction d with
  | zero=>simp
  | succ d ih=>
    rw [Nat.add_succ, pref, ih (Nat.le_add_right n d)]
    simp [lengthAt]

theorem chunks_all (len : Fin n→ℕ) (small : ∀i,len i ≤ p) (pos : 0<q) :
    listMass (chunkRows len small q)=pref len n := by
  have pr:=chunk_mass len small (poolBatchCount n q) le_rfl
  simpa only [←chunkRows_length len small,List.take_length] using
    pr.trans (pref_ended len _ (by simpa [Nat.mul_comm] using CallPool.count_le_batches_mul n q pos))

/-- Each block consists exclusively of the ordered, clipped lengths of
one true neighbor group, with empty final slots encoded as zero. -/
structure GroupBlock {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ}
    (N : Network D P bits) (L : Order N S p) where
  site : Fin S
  other : Fin S
  group : Order.Group L site
  near : group.val=some other

namespace GroupBlock
variable {D S : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} {N : Network D P bits} {L : Order N S p}
def tag (g : GroupBlock N L) := pair g.site g.other
def lengths (g : GroupBlock N L) := groupLengths N L g.site g.group
theorem small (g : GroupBlock N L) (i : Fin (Fintype.card (Order.At L g.site g.group))) :
    g.lengths i ≤ p := by
  unfold lengths groupLengths
  cases ((Order.inGroup L g.site g.group).symm i).val <;> exact Nat.min_le_left ..
def rows (g : GroupBlock N L) (q : ℕ) := chunkRows g.lengths g.small q
end GroupBlock

variable {D S : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)
    (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "L" => order N home native p external nodes ops
local notation "Block" => GroupBlock N L

private theorem has_group (t : ℕ) (live : 0<pairMass N home t) (hp : 0<p) :
    ∃g : Block,g.tag=t := by
  have edge : ∃e : N.Edge,pairIndex N home e=t ∧ 0<N.width e := by
    by_contra! no
    have zero : pairMass N home t=0 := by
      unfold pairMass
      apply Finset.sum_eq_zero
      intro e he
      exact Nat.eq_zero_of_le_zero (no e (Finset.mem_filter.mp he).2)
    omega
  obtain ⟨e,atTag,positive⟩:=edge
  have count:=CallPool.count_le_batches_mul (N.width e) p hp
  have k : 0<poolBatchCount (N.width e) p := by by_contra! no;rw [Nat.eq_zero_of_le_zero no] at count;simp at count;omega
  let name : Names N p:=.inl ⟨e,⟨0,k⟩⟩
  let i:=home (N.src e)
  let j:=home (N.dst e)
  have between : Order.between L i j name := (between_iff N p L i j e ⟨0,k⟩).mpr rfl
  let group : Order.Group L i:=⟨some j,name,between⟩
  exact ⟨⟨i,j,group,rfl⟩,atTag⟩

def selected (hp : 0<p) (t : ℕ) (positive : 0<pairMass N home t) : Block :=
  Classical.choose (has_group N home native external nodes ops t positive hp)

theorem selected_tag (hp : 0<p) (t : ℕ) (positive : 0<pairMass N home t) :
    (selected N home native external nodes ops hp t positive).tag=t :=
  Classical.choose_spec (has_group N home native external nodes ops t positive hp)

/-- Zero-volume pairs contribute no requests to the native stream. -/
def blockRows (q : ℕ) (hp : 0<p) (t : ℕ) : List (Profile q p) :=
  if live : 0<pairMass N home t then (selected N home native external nodes ops hp t live).rows q else []

def stream (q : ℕ) (hp : 0<p) (limit : ℕ) : List (Profile q p) :=
  (List.range limit).flatMap (blockRows N home native external nodes ops q hp)

theorem block_mass (hq : 0<q) (hp : 0<p) (t : ℕ) :
    listMass (blockRows N home native external nodes ops q hp t)=pairMass N home t := by
  unfold blockRows
  split
  · rename_i positive
    let g:=selected N home native external nodes ops hp t positive
    have tg : g.tag=t:=selected_tag N home native external nodes ops hp t positive
    change listMass (chunkRows g.lengths g.small q)=_
    rw [chunks_all _ _ hq,←tg]
    exact group_total N home native external nodes ops hp g.site g.other g.group g.near
  · rename_i zero
    simp [listMass,Nat.eq_zero_of_not_pos zero]

theorem stream_mass (hq : 0<q) (hp : 0<p) (t : ℕ) :
    listMass (stream N home native external nodes ops q hp t)=beforePair N home t := by
  induction t with
  | zero=>simp [stream,listMass,beforePair]
  | succ t ih=>
    rw [stream,List.range_succ,List.flatMap_append,List.flatMap_singleton,mass_append,block_mass N home native external nodes ops hq hp,
      beforePair_succ,←ih]; rfl

/-- All the preceding rows of an actual selected block give its true
dense start, followed by the exact number of bits in earlier local rows. -/
theorem within (hq : 0<q) (hp : 0<p) (t : ℕ) (positive : 0<pairMass N home t)
    (post : List (Profile q p)) (r : ℕ)
    (live : r<poolBatchCount (Fintype.card (Order.At L (selected N home native external nodes ops hp t positive).site
      (selected N home native external nodes ops hp t positive).group)) q) :
    let g:=selected N home native external nodes ops hp t positive
    let pre:=stream N home native external nodes ops q hp t
    let tape:=pre++g.rows q++post
    priorBits tape.get (pre.length+r)=first g.lengths q (pairBase N home g.site g.other) r ∧
      tape[pre.length+r]?=some (rowProfile g.lengths g.small r) := by
  intro g pre tape
  have inside : r<(g.rows q).length := by simpa [GroupBlock.rows] using live
  have room : pre.length+r<tape.length := by simp [tape];omega
  have prefix_take : tape.take (pre.length+r)=pre++(g.rows q).take r := by
    rw [show tape=pre++(g.rows q++post) by simp [tape,List.append_assoc],List.take_append]
    simp [List.take_append_of_le_length (Nat.le_of_lt inside)]
  have total : listMass pre=pairBase N home g.site g.other := by
    change listMass (stream N home native external nodes ops q hp t)=beforePair N home g.tag
    rw [selected_tag N home native external nodes ops hp t positive,stream_mass N home native external nodes ops hq hp]
  refine ⟨?_,?_⟩
  · rw [prior_list _ _ room.le,prefix_take,mass_append,total]
    exact congrArg (_+·) (chunk_mass g.lengths g.small r live.le)
  · rw [show tape=pre++(g.rows q++post) by simp [tape,List.append_assoc]]
    rw [List.getElem?_append_right (Nat.le_add_right pre.length r),
      Nat.add_sub_cancel_left, List.getElem?_append_left inside, List.getElem?_eq_getElem inside]
    simp [GroupBlock.rows,chunkRows]

theorem stream_split (_hq : 0<q) (hp : 0<p) (t limit : ℕ) (less : t<limit) (live : 0<pairMass N home t) :
    ∃post,stream N home native external nodes ops q hp limit=
      stream N home native external nodes ops q hp t++
        (selected N home native external nodes ops hp t live).rows q++post := by
  obtain ⟨d,eqn⟩:=Nat.exists_eq_add_of_le less
  refine ⟨((List.range d).map (t+1+·)).flatMap (blockRows N home native external nodes ops q hp),?_⟩
  simp [eqn,stream,List.range_add (n:=t+1),List.range_succ,blockRows,live,List.append_assoc]

private def packetOf (hp : 0<p) {limit : ℕ} (u : (t : Fin limit) ×
    Fin (blockRows N home native external nodes ops q hp t.val).length) : Packet N L q :=
  if h : 0<pairMass N home u.1.val then
    let g:=selected N home native external nodes ops hp u.1.val h
    ⟨g.site,g.other,g.group,g.near,⟨u.2.val,by
      have bound:=u.2.isLt
      simpa [blockRows,h,GroupBlock.rows,g] using bound⟩⟩
  else False.elim (by have := u.2.isLt;simp [blockRows,h] at this)

private theorem packet_key (hp : 0<p) {limit : ℕ} (u : (t : Fin limit) ×
    Fin (blockRows N home native external nodes ops q hp t.val).length) :
    let a:=packetOf N home native external nodes ops hp u
    pair a.site a.other=u.1.val ∧ a.row.val=u.2.val := by
  intro a
  by_cases h : 0<pairMass N home u.1.val
  · let g := selected N home native external nodes ops hp u.1.val h
    have rowRoom : u.2.val < poolBatchCount (Fintype.card (Order.At L g.site g.group)) q := by
      have bound := u.2.isLt
      simpa [blockRows,h,GroupBlock.rows,g] using bound
    let chosen : Packet N L q := ⟨g.site,g.other,g.group,g.near,⟨u.2.val,rowRoom⟩⟩
    have same : a = chosen := by
      change (packetOf N home native external nodes ops hp u) = chosen
      unfold packetOf
      exact dite_eq_left h
    exact ⟨(congrArg (fun v : Packet N L q => pair v.site v.other) same).trans
      (selected_tag N home native external nodes ops hp u.1.val h),
      congrArg (fun v : Packet N L q => v.row.val) same⟩
  · have := u.2.isLt;simp [blockRows,h] at this

/-- Header input and output are each linear in the purchased port rows.
Zero-volume numerical pair keys never run through the header machine. -/
theorem stream_packets (hp : 0<p) (limit : ℕ) :
    (stream N home native external nodes ops q hp limit).length ≤ Fintype.card (Packet N L q) := by
  let take := packetOf (q:=q) N home native external nodes ops hp (limit:=limit)
  have inj : Function.Injective take := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    have left:=packet_key N home native external nodes ops hp (limit:=limit) (q:=q) ⟨i,a⟩
    have right:=packet_key N home native external nodes ops hp (limit:=limit) (q:=q) ⟨j,b⟩
    have keys:=congrArg (fun u : Packet N L q=>pair u.site u.other) eq
    have atRow:=congrArg (fun u : Packet N L q=>u.row.val) eq
    have same : i=j := Fin.ext (left.1.symm.trans (keys.trans right.1))
    cases same
    have slots : a=b := Fin.ext (left.2.symm.trans (atRow.trans right.2))
    cases slots
    rfl
  have finite:=Fintype.card_le_of_injective take inj
  simp only [Fintype.card_sigma,Fintype.card_fin] at finite
  have length (upto : ℕ) : (stream N home native external nodes ops q hp upto).length=
      ∑t : Fin upto,(blockRows N home native external nodes ops q hp t.val).length := by
    induction upto with
    | zero=>simp [stream]
    | succ a ih=>
      rw [stream,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.length_append,Fin.sum_univ_castSucc]
      exact congrArg (·+_) ih
  rw [length]
  exact finite

theorem paid_length {W : ℕ} (wp : 0<W) (hp : 0<p) (limit : ℕ) :
    (stream N home native external nodes ops q hp limit).length ≤
      DescentTerminalBinPack.purchased W (DescentTerminalRecipeRows.counts (q:=q) (L).site) :=
  (stream_packets N home native external nodes ops hp limit).trans (packet_count N home native external nodes ops wp)

/-- The index and the menu code read by the next physical pass are the
actual two values used by cable fetch at this group and row. -/
theorem native_headers_eof {bitsW : ℕ} (layout : DescentTerminalDenseHeaderRAM.Layout) (m : Memory bitsW)
    (hq : 0<q) (hp : 0<p) (limit : ℕ)
    (fits : DescentTerminalDenseHeaderRAM.Fits layout bitsW (stream N home native external nodes ops q hp limit).length)
    (reads : DescentTerminalDenseHeaderRAM.Reads layout (stream N home native external nodes ops q hp limit).get m) :
    let tape:=stream N home native external nodes ops q hp limit
    ∃after,(DescentTerminalDenseHeaderRAM.program bitsW tape.length layout).Exec m after
      (DescentTerminalDenseHeaderRAM.cost tape.length layout) ∧
      (DescentTerminalDenseHeaderRAM.eof after layout.whole tape.length=
          ((beforePair N home limit/(q*p):ℕ):Word bitsW) ∧
       DescentTerminalDenseHeaderRAM.eof after layout.rem tape.length=
          ((beforePair N home limit%(q*p):ℕ):Word bitsW)) ∧
      ∀(t : ℕ) (_less : t<limit) (positive : 0<pairMass N home t),
      let g:=selected N home native external nodes ops hp t positive
      let pre:=stream N home native external nodes ops q hp t
      ∀r : Fin (poolBatchCount (Fintype.card (Order.At L g.site g.group)) q),
        let request : Packet N L q:=⟨g.site,g.other,g.group,g.near,r⟩
        after (layout.index.base+(pre.length+r.val))=(index N home native external nodes ops request:Word bitsW) ∧
          after (layout.control.base+(pre.length+r.val))=
            ((formatIndex q p (fmt N home native external nodes ops (Nat.mul_pos hq hp) request)).val:Word bitsW) := by
  intro tape
  have pos:=Nat.mul_pos hq hp
  obtain ⟨after,run,state,rowReads⟩:=DescentTerminalDenseHeaderRAM.exec_state layout tape.get pos m fits reads
  have full : priorBits tape.get tape.length=beforePair N home limit := by
    rw [prior_list _ _ le_rfl,List.take_length]
    exact stream_mass N home native external nodes ops hq hp limit
  have eofW:=DescentTerminalDenseHeaderRAM.eof_read after layout.whole
    (DescentTerminalDenseHeaderRAM.wholeVal (bits:=bitsW) tape.get)
    (by simp [DescentTerminalDenseHeaderRAM.wholeVal,prior_zero]) (fun i=>(state i).2)
  have eofR:=DescentTerminalDenseHeaderRAM.eof_read after layout.rem
    (DescentTerminalDenseHeaderRAM.remVal (bits:=bitsW) tape.get)
    (by simp [DescentTerminalDenseHeaderRAM.remVal,prior_zero]) (fun i=>(state i).1)
  refine ⟨after,run,⟨by simpa [DescentTerminalDenseHeaderRAM.wholeVal,full] using eofW,
    by simpa [DescentTerminalDenseHeaderRAM.remVal,full] using eofR⟩,?_⟩
  intro t less positive g pre r packet
  obtain ⟨post,cut⟩:=stream_split N home native external nodes ops hq hp t limit less positive
  obtain ⟨start,profile⟩:=within N home native external nodes ops hq hp t positive post r.val r.isLt
  have tapeEq : tape=pre++g.rows q++post:=cut
  rw [←tapeEq] at start profile
  let i : Fin tape.length:=⟨pre.length+r.val,by
    have h : r.val<(g.rows q).length:=by simp [GroupBlock.rows]
    rw [tapeEq,List.length_append,List.length_append];omega⟩
  have pick : tape.get i=rowProfile g.lengths g.small r.val := by
    rw [List.getElem?_eq_getElem i.isLt] at profile
    exact Option.some.inj profile
  obtain ⟨a,b⟩:=rowReads i
  have startAt : priorBits tape.get i.val=first g.lengths q (pairBase N home g.site g.other) r.val := start
  constructor
  · exact a.trans (congrArg (fun k : ℕ=>((k/(q*p):ℕ):Word bitsW)) startAt)
  · have datum:=control_row g.lengths g.small pos (pairBase N home g.site g.other) r.val
    have residue : (⟨priorBits tape.get i.val%(q*p),Nat.mod_lt _ pos⟩:Fin (q*p))=
        ⟨first g.lengths q (pairBase N home g.site g.other) r.val%(q*p),Nat.mod_lt _ pos⟩ :=
      Fin.ext (congrArg (fun k : ℕ=>k%(q*p)) startAt)
    change after (layout.control.base+i.val)=((formatIndex q p (format g.lengths pos g.small
      (pairBase N home g.site g.other) r.val)).val:Word bitsW)
    rw [b,DescentTerminalDenseHeaderRAM.Header,pick,residue,datum]

theorem native_headers {bitsW : ℕ} (layout : DescentTerminalDenseHeaderRAM.Layout) (m : Memory bitsW)
    (hq : 0<q) (hp : 0<p) (limit : ℕ)
    (fits : DescentTerminalDenseHeaderRAM.Fits layout bitsW (stream N home native external nodes ops q hp limit).length)
    (reads : DescentTerminalDenseHeaderRAM.Reads layout (stream N home native external nodes ops q hp limit).get m) :
    let tape:=stream N home native external nodes ops q hp limit
    ∃after,(DescentTerminalDenseHeaderRAM.program bitsW tape.length layout).Exec m after
      (DescentTerminalDenseHeaderRAM.cost tape.length layout) ∧
      ∀(t : ℕ) (_less : t<limit) (positive : 0<pairMass N home t),
      let g:=selected N home native external nodes ops hp t positive
      let pre:=stream N home native external nodes ops q hp t
      ∀r : Fin (poolBatchCount (Fintype.card (Order.At L g.site g.group)) q),
        let request : Packet N L q:=⟨g.site,g.other,g.group,g.near,r⟩
        after (layout.index.base+(pre.length+r.val))=(index N home native external nodes ops request:Word bitsW) ∧
          after (layout.control.base+(pre.length+r.val))=
            ((formatIndex q p (fmt N home native external nodes ops (Nat.mul_pos hq hp) request)).val:Word bitsW) := by
  intro tape
  obtain ⟨after,run,_,rows⟩:=native_headers_eof N home native external nodes ops layout m hq hp limit fits reads
  exact ⟨after,run,rows⟩

omit [Fintype P] in
theorem beforePair_all (limit : ℕ) (all : ∀e,pairIndex N home e<limit) :
    beforePair N home limit=∑e,N.width e := by simp [beforePair,all]

end
end Hierarchy.DescentTerminalHeaderGroups

end OAI
