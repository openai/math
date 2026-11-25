import OAI.Hierarchy.DescentResetPeerActorChart
import OAI.Hierarchy.DescentResetCompactGeometry
import OAI.Hierarchy.DescentResetTrunkCompactActors

namespace OAI
/-! # Reading truthful old roots and raw palette digits from compact reset rows -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup DescentCommonHost
open DescentResetCompactGeometry DescentActorRaster ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "rad" => (Z).k-(T).commonDepth
local notation "height" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph rad height
local notation "used" => Fintype.card B.next.V
local notation "groups" => S.groupCount (i+1)
variable {H0 H bw : ℕ} (prev : Fintype.card input.V≤H0) (next : Fintype.card B.next.V≤H)
local notation "oldRank" => (vertex).trans (Fin.castLEEmb prev)
local notation "raw" => (Z).rawHostRank T oldRank
local notation "dense" => (Z).denseHostRank T oldRank
local notation "size" => H0*(pal).card
local notation "rankH" => (dense).trans (Fin.castLEEmb next)

theorem compact_geometry_words (st : Store) (base out : ℕ) (m : Memory bw) (here : st.inverse.Fits bw base) (num : (st.count size).Fits bw base)
    (extent : used≤ st.inverse.size) (count : m (st.ranks.base+size)=(used:Word bw))
    (inverse : ∀v:B.next.V,m (st.inverse.base+(dense v).val)=((raw v).val:Word bw))
    (early : base+words size≤out) (space : stop out H<2^bw) :
    let done:=after st.inverse (st.count size) base size (pal).card out H m
    (phase st.inverse (st.count size) base size (pal).card out H bw).Exec m done (ticks st.inverse (st.count size) base size out H) ∧
    (∀v:B.next.V,done ((output out H 0).base+(rankH v).val)=((((Z).rawHostRank T vertex v).val%(pal).card):Word bw) ∧
      done ((output out H 1).base+(rankH v).val)=((oldRank (position (Z).graph v.val)).val:Word bw)) ∧
    (∀h:Fin H,used≤h.val→∀s,done ((output out H s).base+h.val)=0) ∧
    (∀a,a<base ∨ stop out H≤a→done a=m a) ∧ CheapCode (phase st.inverse (st.count size) base size (pal).card out H bw):=by
  intro done
  obtain ⟨exec,cheap_,frame⟩:=any st.inverse (st.count size) base size (pal).card out H m here num early space
  let e:=compactActorOrder B prev
  have actual (j : Fin used) : m (st.inverse.base+j.val)=((compactActorName B prev j).val:Word bw):=by
    have hit:=inverse (e.symm j)
    change m (st.inverse.base+(e (e.symm j)).val)=_ at hit
    rw [e.apply_symm_apply] at hit
    exact hit
  have receipt:=DescentResetCompactGeometry.read st.inverse (st.count size) base size (pal).card out H m used (compactActorName B prev)
    next count actual here num extent early space
  refine ⟨exec,?_,?_,frame,cheap_⟩
  · intro v
    have check (s : Fin 2) : done ((output out H s).base+(rankH v).val)=(value (pal).card s (raw v).val:Word bw):=by
      have lt : (rankH v).val<used:=(dense v).isLt
      have idx : (⟨(rankH v).val,lt⟩:Fin used)=e v:=rfl
      have word := receipt (rankH v) s
      rw [dite_eq_left lt,idx] at word
      have undo : compactActorName B prev (e v)=raw v := by
        change raw (e.symm (e v)) = raw v
        rw [e.symm_apply_apply]
      rw [undo] at word
      exact word
    have pair := compact_host_fields B prev v
    have sizeRoom : size < 2^bw := by
      have rows := DescentResetOriginalSlots.rows_le size
      have endRoom : out ≤ stop out H := Nat.le_add_right ..
      change base+2*DescentResetOriginalSlots.stride size≤out at early
      omega
    have posH : 0 < H0 := Nat.zero_lt_of_lt (oldRank (position (Z).graph v.val)).isLt
    have palRoom : (pal).card < 2^bw := (Nat.le_mul_of_pos_left _ posH).trans_lt sizeRoom
    have rawRoom : (((Z).rawHostRank T vertex) v).val < 2^bw := (raw v).isLt.trans sizeRoom
    have toWord (a b : ℕ) (ha : a < 2^bw) (hb : b < 2^bw) :
        ((a % b : ℕ) : Word bw) = (a : Word bw) % (b : Word bw) := by
      apply Fin.ext
      change (a % b) % 2^bw = (a % 2^bw) % (b % 2^bw)
      rw [Nat.mod_eq_of_lt ((Nat.mod_le a b).trans_lt ha),Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]
    exact ⟨(check 0).trans ((congrArg (fun n : ℕ => (n : Word bw)) pair.1).trans (toWord _ _ rawRoom palRoom)),
      (check 1).trans (congrArg (fun n : ℕ => (n : Word bw)) pair.2)⟩
  · intro h high s;simpa [not_lt_of_ge high] using receipt h s

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
