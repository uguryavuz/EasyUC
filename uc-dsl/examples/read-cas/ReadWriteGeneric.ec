require import UCBasicTypes.
require export Process FMap.

(* Ubiquitous *)
type operation = [Read | Write].
type port_map = (process, port) fmap.

(* For real *)
type pc_id = [R1 | R2 | W1 | W2 | W3].
type local_vars = { x : int option }.
op init_vars = {| x = None |}.
type proc_state = { pc : pc_id; arg : int option ; vars : local_vars }. 
type state_map = (process, proc_state) fmap.

(* For ideal *)
type activity = [Invoked | Linearized].
type ideal_state = { idlst_act : activity; 
                     idlst_op  : operation;
                     idlst_arg : int option;
                     idlst_ret : int option }.
type ideal_state_map = (process, ideal_state) fmap.

(* Simplification hints *)
hint simplify get_set_sameE.
hint simplify set_set_eqE.
hint simplify mem_empty.

lemma mem_set_in (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  x \in m.[x <- y].
proof.
  by rewrite -mem_fdom fdom_set in_fsetU in_fset1.
qed.
hint simplify mem_set_in.

lemma rem_singl_empty (x : 'a, y : 'b) :
  (rem empty.[x <- y] x) = empty.
proof.
  rewrite fdom_eq0 //.
  rewrite fdom_rem fdom_set fdom0.
  by rewrite fset0U fsetDv.
qed.
hint simplify rem_singl_empty.

lemma neq_mem_singl_false (x1 : 'a, x2 : 'a, y : 'b) :
  x1 <> x2 => x1 \notin empty.[x2 <- y].
proof.
  apply contra.
  rewrite mem_set.
  move => [H1 | H2] //.
  by rewrite mem_empty in H1.
qed.
hint simplify neq_mem_singl_false.

lemma nin_rem_set_id (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  x \notin m => rem m.[x <- y] x = m.
proof.
  move => H1.
  apply fmap_eqP.
  move => x0.
  rewrite remE.
  case (x0 = x) => H2.
  + rewrite H2.
    apply get_none in H1.
    by rewrite H1.
  + by apply get_set_neqE.
qed.
hint simplify nin_rem_set_id.

(* Holding area *)
lemma oget_set_eq (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  oget m.[x <- y].[x] = y.
proof.
by rewrite get_set_sameE.
qed.

lemma set_set_last (m : ('a, 'b) fmap, x : 'a, y1 : 'b, y2 : 'b) :
  m.[x <- y1].[x <- y2] = m.[x <- y2].
proof.
rewrite set_set_eqE //.
qed.

lemma mem_empty_false ['a 'b] (x : 'a) :
  x \notin empty<:'a, 'b>.
proof.
rewrite mem_empty //.
qed.
