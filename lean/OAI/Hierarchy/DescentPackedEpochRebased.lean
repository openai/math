import OAI.Hierarchy.DescentSeedVoteEnd
import OAI.Hierarchy.DescentPackedEpochOldAdmit
import OAI.Hierarchy.DescentPackedEpochCountReads

namespace OAI
/-! # Place the mutable profile verdict words beyond the full purchased input -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileValidity DescentPackedProfileInstall DescentPackedEpochFold
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {A : Type} {w : ℕ}

def controlsAt (work lo C r : ℕ) (ss : List (Source A)) (count exterior : ℕ→ℕ) :=
  phases (lo+extent r ss) C r count exterior work (shelves r lo 0 ss)

def oldStateAt (work lo C r seed : ℕ) (ss : List (Source A)) (count : ℕ→ℕ) (z : A→Bool) (m : Memory w) :=
  finalImage z (finalAt work lo r ss) seed (controlsAt work lo C r ss count (fun _=>seed)) m

theorem counter_words_at (work lo C r : ℕ) (count exterior : ℕ→ℕ) (ss : List (Source A)) (m : Memory w) :
    ((controlsAt work lo C r ss count exterior).map fun s=>(m s.banks.count.base).val)=
      (List.range' 0 ss.length).map (fun j=>(m (count j)).val) := by
  have rows := count_addresses (lo + extent r ss) C r work count exterior (shelves r lo 0 ss)
  rw [ordinals] at rows
  simpa only [controlsAt, List.map_map, Function.comp_def] using
    congrArg (fun addrs : List ℕ => addrs.map fun i => (m i).val) rows

theorem readyAt (work lo C r seed : ℕ) (ss : List (Source A)) (count exterior : ℕ→ℕ) (z : A→Bool) (old : Memory w)
    (same : DescentTerminalEpochDecoder.Uniform C ss) (pos : 0 < r) (first : seed < lo)
    (below : ∀p∈shelves r lo 0 ss,count p.ordinal < lo ∧ exterior p.ordinal < lo)
    (past : end_ (lo+extent r ss) C r ≤ work) (wide : ∀s∈ss, slots s.seats r*r < 2^w) (room : finalAt work lo r ss+1 < 2^w) :
    let start:=end_ (lo+extent r ss) C r
    let ts:=controlsAt work lo C r ss count exterior
    let m:=header lo C r ss z old
    Order w work seed (finalAt work lo r ss) ts ∧ (∀s∈ts,Paid w start s) ∧
      (∀s∈ts,Reads s.banks m s.source.pin z s.grain) ∧ ts.map Stage.source=ss := by
  let ps:=shelves r lo 0 ss
  let table:=lo+extent r ss
  let o:=end_ table C r
  let ts:=controlsAt work lo C r ss count exterior
  have late : o ≤ work:=past
  have tableTop : table ≤ o:=by change table ≤ (table+_)+_;omega
  have oldLo : lo ≤ table:=Nat.le_add_right _ _
  have outFit : work+(ps.map (stepRows r)).sum+1 < 2^w:=room
  have limits (p : Shelf A) (hp : p∈ps) : tablesBase p.base p.src.seats r ≤ table :=
    (next p.base r p.src).trans_le (placed r lo 0 ss p hp).2
  have in_ (p : Shelf A) (hp : p∈ps) : p.src∈ss:=sources r lo 0 ss ▸ List.mem_map_of_mem (f:=Shelf.src) hp
  refine ⟨order table C r count exterior work work seed ps (by omega) le_rfl outFit,?_,?_,
    (phase_sources table C r count exterior work ps).trans (sources r lo 0 ss)⟩
  · intro s hs
    obtain ⟨p,hp,src,bs,grain,ext,low,dest,ending⟩:=phase_mem table C r count exterior work ps s hs
    have pc:=below p hp
    have e:=limits p hp
    have uniform:=same _ (in_ p hp)
    have srcLo : lo ≤ p.base:=(placed r lo 0 ss p hp).1
    let S:=sourceBank p.base p.src.seats r
    let T:=startsBank p.base p.src.seats r
    let B:=shifts table r
    let D:=dict table C r
    have S₀ : S.base+S.size=T.base:=rfl
    have T₀ : T.base+T.size ≤ table:=e
    have B₀ : B.base=table:=rfl
    have B₁ : B.base+B.size=D.base:=rfl
    have D₀ : D.base+D.size=o:=rfl
    have fit (bank : Bank) (bounds : bank.base+bank.size ≤ o) : bank.Fits w s.out :=
      ⟨Nat.two_pow_pos _,by omega,by omega⟩
    have exteriorLow : s.exterior < o := by
      rw [ext]
      exact pc.2.trans_le (oldLo.trans tableTop)
    refine ⟨?_,grain.symm ▸ pos,late.trans low,exteriorLow,?_,by omega,?_⟩
    · rw [bs,src,grain,uniform]
      exact ⟨fit S (by omega),fit T (by omega),fit B (by omega),fit D (by omega),
        fit ⟨count p.ordinal,0⟩ (by change count p.ordinal+1 ≤ o;omega),Nat.le_pow_clog (by decide) _,
        Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,
        wide _ (in_ p hp),by omega⟩
    · rw [dest,rows,src,grain]
    · intro bank mem
      rw [bs] at mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with h|h|h|h|h <;> subst bank
      · change S.base+S.size ≤ o;omega
      · change T.base+T.size ≤ o;omega
      · change B.base+B.size ≤ o;omega
      · change D.base+D.size ≤ o;omega
      · change count p.ordinal+1 ≤ o;omega
  · intro s hs
    obtain ⟨p,hp,src,bs,grain,_⟩:=phase_mem table C r count exterior work ps s hs
    rw [src,bs,grain]
    exact stored lo C r ss z old same p hp (count p.ordinal)
theorem data_after_at {S Z U : Type} {bits : Z→ S→ Bool} {ok : (S→ Bool)→ Prop} {fd : U→ Z}
    (b : Chart bits ok fd) (z : b.Pin→ Bool) (old m : Memory w) (work lo C r seed : ℕ) (count exterior : ℕ→ℕ)
    (same : DescentTerminalEpochDecoder.Uniform C b.layout) (pos : 0 < r) (seedLow : seed < lo)
    (lower : ∀p∈shelves r lo 0 b.layout,count p.ordinal < lo ∧ exterior p.ordinal < lo)
    (past : end_ (lo+extent r b.layout) C r ≤ work) (wide : ∀s∈b.layout,slots s.seats r*r < 2^w) (room : finalAt work lo r b.layout+1 < 2^w)
    (retained : ∀a,lo ≤ a→ a < end_ (lo+extent r b.layout) C r→ m a=header lo C r b.layout z old a)
    : let ts:=controlsAt work lo C r b.layout count exterior
      let _base:=end_ (lo+extent r b.layout) C r
      Order w work seed (finalAt work lo r b.layout) ts ∧
      (∀s∈ts,Paid w work s) ∧ (∀s∈ts,Reads s.banks m s.source.pin z s.grain) ∧ ts.map Stage.source=b.layout := by
  let head:=lo+extent r b.layout
  let out:=end_ head C r
  let ts:=controlsAt work lo C r b.layout count exterior
  obtain ⟨seq,pr,initial,domain⟩:=readyAt work lo C r seed b.layout count exterior z old same pos seedLow lower past wide room
  refine ⟨seq,?_,?_,domain⟩
  · intro s hs
    have orig:=pr s hs
    obtain ⟨p,hp,_,_,_,_,late,_⟩:=phase_mem head C r count exterior work (shelves r lo 0 b.layout) s hs
    exact ⟨orig.space,orig.positive,late,orig.ext.trans_le past,orig.mid,orig.end_,fun b hb=>(orig.retained b hb).trans past⟩
  intro s hs
  apply held_reads s lo out z _ m (pr s hs) _ retained (initial s hs)
  obtain ⟨p,hp,_,bs,_⟩:=phase_mem head C r count exterior work (shelves r lo 0 b.layout) s hs
  have low:=(placed r lo 0 b.layout p hp).1
  have high : lo ≤ head:=Nat.le_add_right _ _
  intro bank hb
  rw [bs] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h|h|h|h <;> subst bank
  · exact low
  · exact low.trans (Nat.le_add_right _ _)
  · exact high
  · exact high.trans (Nat.le_add_right _ _)

theorem oldAdmitAt {S Z U : Type} {bits : Z→ S→ Bool} {ok : (S→ Bool)→ Prop} {fd : U→ Z}
    (b : Chart bits ok fd) (z : b.Pin→ Bool) (old m : Memory w) (work lo C r seed : ℕ) (count : ℕ→ℕ)
    (same : DescentTerminalEpochDecoder.Uniform C b.layout) (pos : 0 < r) (seedLow : seed < lo)
    (lower : ∀p∈shelves r lo 0 b.layout,count p.ordinal < lo)
    (past : end_ (lo+extent r b.layout) C r ≤ work) (wide : ∀s∈b.layout,slots s.seats r*r < 2^w) (space : finalAt work lo r b.layout+1 < 2^w)
    (held : ∀a,lo ≤ a→ a < end_ (lo+extent r b.layout) C r→ m a=header lo C r b.layout z old a)
    (seeded : m seed=0 ↔ ok (z∘b.seed))
    (counts : List.IsPrefix ((b.rows z).map Observation.count)
      ((controlsAt work lo C r b.layout count (fun _=>seed)).map fun s=>(m s.banks.count.base).val)) :
    let ss:=controlsAt work lo C r b.layout count (fun _=>seed)
    let dst:=finalAt work lo r b.layout
    let o:=oldStateAt work lo C r seed b.layout count z m
    (fold w seed dst ss).Exec m o (bill seed dst ss) ∧ CheapCode (fold w seed dst ss) ∧
    (o dst=0 ↔ ∃c,b.read z=some c) ∧ ∀a < work,o a=m a := by
  let ext : ℕ→ℕ:=fun _=>seed
  let ss:=controlsAt work lo C r b.layout count ext
  let dst:=finalAt work lo r b.layout
  let base:=work
  obtain ⟨safe,pr,data_,domain⟩:=data_after_at b z old m work lo C r seed count ext same pos seedLow
    (fun q h=>⟨lower q h,seedLow⟩) past wide space held
  have exact_:=exact_run base seed dst ss z m safe pr data_
  have test:=survives b z m ss seed seeded domain counts
  have ports (s : Stage b.Pin) (hs : s∈ss) : s.exterior=seed := by
    obtain ⟨p,hp,src,bs,g,ex,_⟩:=phase_mem (lo+extent r b.layout) C r count ext base
      (shelves r lo 0 b.layout) s hs
    exact ex
  have neq:=one_ne (w:=w) (by omega)
  refine ⟨exact_.1,(run base seed dst ss z m safe pr data_).2,?_,exact_.2.2⟩
  change finalImage z dst seed ss m dst=0 ↔ _
  rw [exact_.2.1]
  constructor
  · intro zero
    by_contra no
    have dead : ¬(m seed=0 ∧ ∀s∈ss,m s.exterior=0 ∧ (view s m z).Valid) := fun h=>no (test.mp h).1
    exact neq (by simpa only [ite_eq_right dead] using zero)
  · intro chosen
    have live:=seeded.mpr ((b.accepted z).mp chosen).1
    exact ite_eq_left (test.mpr ⟨chosen,fun s h=>(congrArg m (ports s h)).trans live⟩)

theorem oldStateAt_frame {S Z U : Type} {bits : Z→ S→ Bool} {ok : (S→ Bool)→ Prop} {fd : U→ Z}
    (b : Chart bits ok fd) (z : b.Pin→ Bool) (old m : Memory w) (work lo C r seed : ℕ) (count : ℕ→ℕ)
    (same : DescentTerminalEpochDecoder.Uniform C b.layout) (pos : 0 < r) (seedLow : seed < lo)
    (lower : ∀p∈shelves r lo 0 b.layout,count p.ordinal < lo)
    (past : end_ (lo+extent r b.layout) C r ≤ work) (wide : ∀s∈b.layout,slots s.seats r*r < 2^w) (space : finalAt work lo r b.layout+1 < 2^w)
    (held : ∀a,lo ≤ a→ a < end_ (lo+extent r b.layout) C r→ m a=header lo C r b.layout z old a)
    (a : ℕ) (away : a < work ∨ finalAt work lo r b.layout < a) :
    oldStateAt work lo C r seed b.layout count z m a=m a := by
  obtain ⟨safe,paid,data_,_⟩:=data_after_at b z old m work lo C r seed count (fun _=>seed) same pos seedLow
    (fun q h=>⟨lower q h,seedLow⟩) past wide space held
  rcases away with low|high
  · exact (exact_run _ _ _ _ z m safe paid data_).2.2 a low
  · exact high_frame z m safe paid high

theorem bill_at (work lo C r seed : ℕ) (ss : List (Source A)) (count exterior : ℕ→ℕ) :
    bill seed (finalAt work lo r ss) (controlsAt work lo C r ss count exterior)=
      bill seed (final lo C r ss) (controls lo C r ss count exterior) := by
  rw [bill_eq,bill_eq]
  have row_ : (controlsAt work lo C r ss count exterior).map rows=(controls lo C r ss count exterior).map rows := by
    unfold controlsAt controls
    rw [phase_rows,phase_rows]
  have len:=congrArg List.length row_
  simp only [List.length_map] at len
  rw [len,row_]

end
end Hierarchy.DescentPackedEpochShelves

end OAI
