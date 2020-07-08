(* UcExpressions module interface *)

open UcTypes
open UcSpec

val check_expression : (qid -> typ) -> expression_l -> typ
val is_distribution : typ -> bool
val get_distribution_typ : typ -> typ
