
open MyUtil

type input_kind =
  | SATySFi
  | Markdown of string

type output_mode =
  | PdfMode
  | TextMode of string list

type build_state = {
  input_file             : abs_path;
  output_file            : abs_path option;
  input_kind             : input_kind;
  output_mode            : output_mode;
  page_number_limit      : int;
  debug_show_bbox        : bool;
  debug_show_space       : bool;
  debug_show_block_bbox  : bool;
  debug_show_block_space : bool;
  debug_show_overfull    : bool;
  type_check_only        : bool;
  bytecomp               : bool;
}

type command_state =
  | BuildState of build_state
  | SolveState

type state = {
  command_state      : command_state;
  extra_config_paths : (string list) option;
  show_full_path     : bool;
  show_fonts         : bool;
  no_default_config  : bool;
}


let state = ref None


let set r =
  state := Some(r)


let get () =
  match !state with
  | None    -> assert false
  | Some(r) -> r


let get_build_state () =
  match (get ()).command_state with
  | BuildState(b) -> b
  | _             -> assert false


let get_input_file ()              = (get_build_state ()).input_file
let get_output_file ()             = (get_build_state ()).output_file
let get_extra_config_paths ()      = (get ()).extra_config_paths
let get_output_mode ()             = (get_build_state ()).output_mode
let get_input_kind ()              = (get_build_state ()).input_kind
let get_page_number_limit ()       = (get_build_state ()).page_number_limit
let does_show_full_path ()         = (get ()).show_full_path
let does_debug_show_bbox ()        = (get_build_state ()).debug_show_bbox
let does_debug_show_space ()       = (get_build_state ()).debug_show_space
let does_debug_show_block_bbox ()  = (get_build_state ()).debug_show_block_bbox
let does_debug_show_block_space () = (get_build_state ()).debug_show_block_space
let does_debug_show_overfull ()    = (get_build_state ()).debug_show_overfull
let is_type_check_only ()          = (get_build_state ()).type_check_only
let is_bytecomp_mode ()            = (get_build_state ()).bytecomp
let does_show_fonts ()             = (get ()).show_fonts
let use_no_default_config ()       = (get ()).no_default_config


let job_directory () =
  let abspath = get_input_file () in
  Filename.dirname (get_abs_path_string abspath)


let is_text_mode () =
  match (get_build_state ()).output_mode with
  | TextMode(_) -> true
  | PdfMode     -> false
