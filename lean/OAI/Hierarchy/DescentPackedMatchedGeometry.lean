import OAI.Hierarchy.DescentMarkedNeighborToken
import OAI.Hierarchy.DescentPackedMatchedGather
import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentPackedActorRaster

namespace OAI
/-! # Authentic site tickets and marked old-edge occurrences in the packed matching panel -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.PackedCensus DescentSIMDLookup DescentSharedCableNames
open scoped Classical
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
local notation "Host" => DescentSharedCableNames.Stage.Host J V k
variable (names : DescentSharedCableNames.Stage.Host J V k ↪ ℕ)

def gated {k d s : ℕ} (active : Cell (1*2^k)) (x : Fin (2^k)) (win : Cell d) : Cell s :=
  if digit 1 x.val active.val=1 then word s win.val else 0

/-- Read the actor raster separately so a real isolated old site retains its
proper position in the ordered thin stream. -/
def terrain (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : DescentSharedCableNames.Stage.Host J V k↪ℕ)
    {a : ℕ} (win : J×V→Fin (2^k)→Cell a) (next : (J×V)→Fin A.degree→Option (J×V)) (h : J×V) :
    Panel (2^k) A.degree (2*A.cap) short where
  winner x := gated (DescentActorRaster.actorMask A.pos A.block h) x (win h x)
  neighbor x s := marked short (DescentSharedCableNames.Stage.signedPanel A native S ready names (h,x) s)
  peerWinner v x := (next h v).elim 0 fun h'=>gated (DescentActorRaster.actorMask A.pos A.block h') x (win h' x)

variable {a : ℕ} (win : J×V→Fin (2^k)→Cell a) (next : (J×V)→Fin A.degree→Option (J×V))

theorem real_winner (u : W.graph.Site) (fits : (win (A.pos u) (A.block u)).val<2^short) :
    ((terrain (short:=short) A native S ready names win next (A.pos u)).winner (A.block u)).val=(win (A.pos u) (A.block u)).val := by
  change (gated (s:=short) (DescentActorRaster.actorMask A.pos A.block (A.pos u))
    (A.block u) (win (A.pos u) (A.block u))).val = _
  have exists_ : ∃v,A.pos v=A.pos u ∧ A.block v=A.block u := ⟨u,rfl,rfl⟩
  simp [gated,DescentActorRaster.actor_read,exists_,word,Nat.mod_eq_of_lt fits]

theorem empty_winner (h : J×V) (x : Fin (2^k)) (empty : ¬∃v,A.pos v=h ∧ A.block v=x) :
    (terrain (short:=short) A native S ready names win next h).winner x=0  := by
  change gated (s:=short) (DescentActorRaster.actorMask A.pos A.block h) x (win h x) = 0
  simp [gated,DescentActorRaster.actor_read,empty]

/-- The local source slot belonging to the marked first grain of an actual old edge. -/
def address (h : Host) := (PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h.1 h.2).trans
  (DescentSharedCableNames.Stage.signed A native S ready h.1 h.2)

def target (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : DescentSharedCableNames.Stage.Host J V k↪ℕ)
    (h : Host) (e : PackedCensus.Out W A.pos A.block h.1 h.2) : Fin A.degree :=
  (DescentSharedCableNames.Stage.live A native S ready names h
    (PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h.1 h.2 e)).neighbor

theorem source_order (h : Host) (e f : PackedCensus.Out W A.pos A.block h.1 h.2) :
    address A native S ready h e<address A native S ready h f ↔ native e.val<native f.val := by
  constructor
  · intro less
    rcases lt_trichotomy (native e.val) (native f.val) with hlt|eqn|hlt
    · exact hlt
    · exact False.elim ((ne_of_lt less) (congrArg (address A native S ready h) (Subtype.ext (native.injective eqn))))
    · exact False.elim ((not_lt_of_ge less.le) (DescentSharedCableNames.Stage.out_before A native S ready h f e hlt))
  · exact DescentSharedCableNames.Stage.out_before A native S ready h e f

theorem source_wire (h : Host) (e : PackedCensus.Out W A.pos A.block h.1 h.2) :
    (address A native S ready h e).val=
      (DescentSharedCableNames.Stage.outgoing A native S ready ⟨e.val,A.quantum_positive e.val e.property.2⟩).val := by
  let B:=DescentSharedCableNames.Stage.source A native
  let q:=PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h.1 h.2 e
  let pos:=B.position (DescentSharedCableNames.Stage.measured A native S ready) h
  have first : (address A native S ready h e).val=(pos (DescentSharedCableNames.Stage.ofPort A native h q)).val := by
    change (finProdFinEquiv ((0:Fin 2),pos (DescentSharedCableNames.Stage.ofPort A native h q))).val=_
    simp [finProdFinEquiv_apply_val]
  rw [first]
  have here : DescentSharedCableNames.Stage.home A (W.graph.src e.val)=h := Prod.ext e.property.1.1 e.property.1.2
  let wire : DescentSharedCableNames.Stage.Positive A:=⟨e.val,A.quantum_positive e.val e.property.2⟩
  have atHome (z : Host) (c : DescentSharedCableNames.Stage.Positive A) (hit : DescentSharedCableNames.Stage.home A (W.graph.src c.val)=z) :
      DescentSharedCableNames.Stage.outgoingAt A native S ready z c hit=DescentSharedCableNames.Stage.outgoing A native S ready c := by subst z;rfl
  exact congrArg Fin.val (atHome h wire here)

theorem marked_read (h : Host) (e : PackedCensus.Out W A.pos A.block h.1 h.2) (fit : A.degree<2^short) :
    ((terrain (short:=short) A native S ready names win next h.1).neighbor h.2 (address A native S ready h e)).val=(target A native S ready names h e).val+1 := by
  let pick := PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h.1 h.2
  have tag : DescentSharedCableNames.Stage.isMarkedOut A h (pick e)=true :=
    (DescentSharedCableNames.Stage.marked_iff A h (pick e)).mpr ⟨e,rfl⟩
  have bound : (target A native S ready names h e).val+1<2^short := (Nat.succ_le_of_lt (target A native S ready names h e).isLt).trans_lt fit
  change (marked short (DescentSharedCableNames.Stage.signedPanel A native S ready names h
    (DescentSharedCableNames.Stage.signed A native S ready h.1 h.2 (pick e)))).val=_
  rw [DescentSharedCableNames.Stage.signed_read]
  change (if DescentSharedCableNames.Stage.isMarkedOut A h (pick e) then word short ((target A native S ready names h e).val+1) else 0).val=_
  simp only [tag,ite_true,word]
  exact Nat.mod_eq_of_lt bound

theorem peer_at (h : Host) (e : PackedCensus.Out W A.pos A.block h.1 h.2) (fit : A.degree<2^short) :
    peer (terrain (short:=short) A native S ready names win next h.1) h.2 (address A native S ready h e)=some (target A native S ready names h e) := by
  have decode {r deg count width : ℕ} (panel : Panel r deg count width)
      (x : Fin r) (slot : Fin count) (v : Fin deg)
      (read : (panel.neighbor x slot).val = v.val + 1) : peer panel x slot = some v := by
    have valid : 0 < (panel.neighbor x slot).val ∧ (panel.neighbor x slot).val ≤ deg := by
      rw [read]
      exact ⟨Nat.zero_lt_succ _, v.isLt⟩
    simp only [peer, dite_eq_left valid, Option.some.injEq]
    apply Fin.ext
    change (panel.neighbor x slot).val - 1 = v.val
    rw [read, Nat.add_sub_cancel]
  exact decode _ _ _ _ (marked_read A native S ready names win next h e fit)

theorem other_port (h : Host) (s : Fin (2*A.cap)) (absent : ∀e,address A native S ready h e≠s) :
    (terrain (short:=short) A native S ready names win next h.1).neighbor h.2 s=0 := by
  let addr := DescentSharedCableNames.Stage.signed A native S ready h.1 h.2
  change marked short (DescentSharedCableNames.Stage.signedPanel A native S ready names h s)=0
  by_cases occurs : ∃p,addr p=s
  · obtain ⟨p,hp⟩ := occurs
    have read := DescentSharedCableNames.Stage.signed_read A native S ready names h p
    change DescentSharedCableNames.Stage.signedPanel A native S ready names h (addr p) = _ at read
    rw [hp] at read
    rw [read]
    have clear : DescentSharedCableNames.Stage.isMarkedOut A h p=false := by
      cases tag : DescentSharedCableNames.Stage.isMarkedOut A h p with
      | false => rfl
      | true =>
        obtain ⟨e,hit⟩ := (DescentSharedCableNames.Stage.marked_iff A h p).mp tag
        exact (absent e ((congrArg addr hit).trans hp)).elim
    change (if DescentSharedCableNames.Stage.isMarkedOut A h p then
      word short ((DescentSharedCableNames.Stage.live A native S ready names h p).neighbor.val+1)
      else 0) = 0
    simp only [clear, Bool.false_eq_true, ite_false]
  · rw [DescentSharedCableNames.Stage.signed_empty A native S ready names h s (not_exists.mp occurs)]
    rfl

theorem all_ports (h : Host) (s : Fin (2*A.cap)) (v : Fin A.degree) (fit : A.degree<2^short) :
    peer (terrain (short:=short) A native S ready names win next h.1) h.2 s=some v ↔ ∃e,address A native S ready h e=s ∧ target A native S ready names h e=v := by
  by_cases leaf : ∃e,address A native S ready h e=s
  · obtain ⟨e,rfl⟩ := leaf
    rw [peer_at A native S ready names win next h e fit]
    simp only [Option.some.injEq,Function.Embedding.apply_eq_iff_eq,exists_eq_left]
  · have absent : ∀ e, address A native S ready h e ≠ s := not_exists.mp leaf
    have missing : peer (terrain (short:=short) A native S ready names win next h.1) h.2 s = none := by
      simp [peer, other_port A native S ready names win next h s absent]
    constructor
    · intro seen
      rw [missing] at seen
      cases seen
    · rintro ⟨e, hit, _⟩
      exact (absent e hit).elim


end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
