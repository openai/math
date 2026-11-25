import OAI.Hierarchy.DescentTerminalMeterAdmission
import OAI.Hierarchy.DescentTerminalFullAddress
import OAI.Hierarchy.DescentTerminalEmitterFront

namespace OAI
/-! # A placed terminal uses its own native two-word parity initialization -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalRowArena
open DescentTerminalEmitter.Allocation (parity)
open scoped Fin.CommRing
noncomputable section
variable {blocks w : ℕ} (S:Shape) (I:Input) (base:ℕ)
local notation "A" => rowArena S I base
variable (F:MaskedShelf blocks) (O:DescentPrivateExponentRAM.Banks)
local notation "L" => layout S I base O

/-- Any earlier dated header and both newly issued parity bytes are preserved by all
subsequent row-plan, slot-sort, scalar-page and leaf-event writes. -/
theorem before (x:ℕ) (low:x<(A).start+2) :
    Suffix.Early S L x := by
  have st:=(A).stride_min
  change 2*S.sites+_+_+1<(A).stride at st
  have positive:=S.sites_pos
  have bound (j:ℕ) (hj:1≤j) : x<(A).atBand j:=by
    have le:=Nat.mul_le_mul_right (A).stride hj
    simp only [one_mul] at le
    change x<(A).start+j*(A).stride
    omega
  have pageLo:x<(A).finish:=bound 22 (by decide)
  have eventLo : x<(events A S.terminal.pool).base:=by change x<(A).finish+_;omega
  have event : (inputs S I base 40).base=(events A S.terminal.pool).base:=by simp [inputs]
  refine ⟨⟨⟨bound 9 (by decide),bound 7 (by decide),bound 6 (by decide),bound 5 (by decide),
      bound 4 (by decide),bound 3 (by decide)⟩,bound 2 (by decide),bound 13 (by decide),
      bound 14 (by decide),?_⟩,?_,pageLo⟩
  · change x<(inputs S I base 40).base;simpa only [event] using eventLo
  · change x<(A).atBand 17+_+_;have:=bound 17 (by decide);omega

def tailCode := ((A).prime w).seq (Suffix.program (w:=w) S L F)
def tailImage (m:Memory w) := Suffix.output S L F ((A).mount m)

private theorem parity_frame (j : Fin 2) :
    DescentTerminalEmitter.BeforeKey S.terminal (L).emit ((A).start+j.val) ∧
    DescentTerminalEmitter.AfterFlights S.terminal (L).emit ((A).start+j.val) := by
  obtain ⟨p0,p1,p2,_,_⟩ := stages S I base
  have h:=before S I base O ((A).start+j.val) (by have:=j.isLt;omega)
  have hbase:(A).start+j.val<(A).finish:=h.page
  have phase:(A).start+j.val<takeOff S I base:=hbase.trans_le (p0.trans p1)
  let s:=S.terminal.plane
  let orig:=takeOff S I base
  let limit:=DescentTerminalDataPlane.Arena.finish s orig
  have src : (A).start+j.val<DescentTerminalEmitter.Allocation.front limit
      (bodyPlane S I base) (publicHeader S I base) := by
    unfold DescentTerminalEmitter.Allocation.front
    simp only [lt_min_iff]
    change _<orig ∧ _<orig+24*_ ∧ _<orig+24*_+_ ∧ _<_+0*_ ∧ _<_+0*_ ∧ _<limit
    have h2:(A).start+j.val<DescentTerminalDataPlane.Arena.headerBase s orig:=by change _<orig+24*_+_+_;omega
    have h3:(A).start+j.val<DescentTerminalDataPlane.Arena.second s orig:=by change _<DescentTerminalDataPlane.Arena.headerBase s orig+4*_;omega
    exact ⟨phase,by omega,by omega,by simpa using h2,by simpa using h3,phase.trans_le p2⟩
  exact DescentTerminalEmitter.Allocation.original_frame S.terminal I.indexEvents I.formatEvents limit
    (inputs S I base) (bodyPlane S I base) (publicHeader S I base) I.blank src

theorem tail_run (m:Memory w) (old:Earlier S I base F w) (end_:endAddress S I base<2^w)
    (positive:0<w) :
    (tailCode S I base F O (w:=w)).Exec m (tailImage S I base F O m)
       ((8+104*S.sites)+Suffix.time S L blocks) ∧ CheapCode (tailCode S I base F O (w:=w)) := by
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I base
  have room:=suffix_room S I base F O old end_
  have startOk:=p0.trans_lt (p1.trans_lt (p2.trans_lt (p3.trans_lt (p4.trans_lt end_))))
  let M:=Suffix.events S L F ((A).mount m)
  have literals (j:Fin 2) : M ((A).start+j.val)=(j.val:Word w) := by
    have hj:=j.isLt
    have hH:=S.sites_pos
    have keep:=before S I base O _ (show (A).start+j.val<(A).start+2 by omega)
    rw [show M ((A).start+j.val)=(A).mount m ((A).start+j.val) from
       Suffix.early S L F _ room keep.original keep.slot keep.page]
    simpa only [Arena.atBand, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hj] using (A).mount_low m (i:=j.val) (by change j.val<2*S.sites;omega)
  have emit : DescentTerminalEmitter.Static S.terminal (L).emit M :=
    DescentTerminalEmitter.Allocation.installed_parity S.terminal I.indexEvents I.formatEvents
      (DescentTerminalDataPlane.Arena.finish S.terminal.plane (takeOff S I base)) (inputs S I base)
      (bodyPlane S I base) (publicHeader S I base) I.blank M room.issuer positive (A).start
      (by simp [inputs]) (by simp [inputs]) (by simp [inputs]) literals (parity_frame S I base O)
  have rest:=Suffix.run S L F ((A).mount m) room positive ((A).mounted_fixed startOk m) emit
  have init:=(A).prime_run m startOk
  exact exec_cheap_seq init rest

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
