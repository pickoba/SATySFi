(* module Mcdout *)
  open Types

  let report_error errmsg =
    print_string ("! [ERROR IN OUT] " ^ errmsg ^ ".") ; print_newline ()

  (* abstract_tree -> string *)
  let rec mcdout value =
    mcdout_sub 0 value

  (* int -> abstract_tree -> string *)
  and mcdout_sub indent value =
    match value with
      EmptyAbsBlock -> ""

    | AbsBlock(value_former, value_latter) ->
        (mcdout_sub indent value_former) ^ (mcdout_sub indent value_latter)

    | Output(c) -> c

    | DeeperIndent(value_content) -> mcdout_sub (indent + 1) value_content

    | BreakAndIndent -> "\n" ^ (if indent > 0 then String.make (indent * 2) ' ' else "")

    | Separated(vf, vl) -> ( report_error "cannot output '|'" ; raise IllegalOut )

    | _ -> raise IllegalOut
