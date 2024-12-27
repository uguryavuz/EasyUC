require import UCBasicTypes.
require export Process FMap.

(* Ubiquitous *)
type operation = [Read | Write].
type port_map = (process, port) fmap.

(* For real *)
type pc_id = [R1 | R2 | W1 | W2 | W3].
(* type local_vars = (string, int) fmap. *)
type local_vars = { x : int option }.
op init_vars = {| x = None |}.
type proc_state = { pc : pc_id; arg : int option ; vars : local_vars }. 
type state_map = (process, proc_state) fmap.
