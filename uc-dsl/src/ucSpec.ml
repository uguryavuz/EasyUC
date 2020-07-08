(* UcSpec module *)

(* Specification Parse Trees *)

open EcLocation

exception ParseError of EcLocation.t * string option
let parse_error loc msg = raise (ParseError (loc, msg))

exception ParseError2 of EcLocation.t * EcLocation.t * string
let parse_error2 loc1 loc2 msg = raise (ParseError2 (loc1, loc2, msg))

type string_l = string located

type id = string_l

type msg_in_out =
  | In
  | Out

type ty =
  | NamedTy of id
  | TupleTy of ty list

type name_type = {id : id; ty : ty}

type message_def =
  {direction : msg_in_out; id : id; content : name_type list;
   port_label: id option}

type basic_io_body = message_def list

type io_item = {id : id; io_id : id}

type composite_io_body = io_item list

type io_body =
  | Basic     of basic_io_body
  | Composite of composite_io_body

type io = {id : id; body : io_body}

type io_def =
  | DirectIO      of io
  | AdversarialIO of io

type fun_param = {id : id; id_dir_io : id}

type sub_fun_decl = {id : id; fun_id : id; fun_param_ids: id list}

type msg_type =
  | MsgType  of id
  | OtherMsg of EcLocation.t

type qid = id list

type msg_path = {io_path: qid; msg_type : msg_type}

type match_item =
  | Const of id
  | ConstType of name_type
  (*| Tuple of match_item list located*)
  | Wildcard of EcLocation.t

type msg_match =
  {port_var : id option; path : msg_path; tuple_match : match_item list option}

type expression =
  | Id    of qid
  | Tuple of expression_l list
  | App   of id * expression_l list
  | Enc   of expression_l

and expression_l = expression located

type msg_instance =
  {path : msg_path; tuple_instance : expression_l list; port_var : id option}

type state_instance = {id : id; params : expression_l list option}

type send_and_transition = {msg : msg_instance; state : state_instance}

type instruction =
  | Assign of id * expression_l
  | Sample of id * expression_l
  | ITE of expression_l * instruction_l list * instruction_l list option
  | Decode of
      expression_l * ty * match_item list * instruction_l list *
      instruction_l list
  | SendAndTransition of send_and_transition
  | Fail

and instruction_l = instruction located

type msg_match_code = {pattern_match : msg_match; code: instruction_l list;}

type state_code = {vars : name_type list; mmcodes : msg_match_code list}

type state = {id : id; params : name_type list ; code : state_code}
                
type state_def =
  | InitialState of state
  | FollowingState of state 

type party_def = {id : id; serves : qid list; code : state_def list}

type sub_item =
  | SubFunDecl of sub_fun_decl
  | PartyDef of party_def

(*either state_body is empty or both params and body are empty*)
type fun_def =
  {id : id; params : fun_param list; id_dir_io : id; id_adv_io : id option;
   body : sub_item list; state_body : state_def list}

type sim_def =
  {id : id; uses : id; sims : id; sims_param_ids: id list;
   body : state_def list }

type def =
  | IODef  of io_def
  | FunDef of fun_def
  | SimDef of sim_def

type externals = {ec_requirements : id list; dl_imports : id list}

type spec = {externals : externals; definitions : def list}