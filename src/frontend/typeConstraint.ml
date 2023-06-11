open Types

let solve_constraint_expr (unifier : mono_type -> mono_type -> (unit, TypeError.unification_error) result) ((_, con) : mono_type_constraint_expr) : (unit, TypeError.type_error) result =
  match con with
  | ConstraintEqual(lhs, rhs) ->
      unifier lhs rhs
      |> Result.map_error (fun uerr -> TypeError.TypeUnificationError(lhs, rhs, uerr))


let try_constraint_expr (con : mono_type_constraint_expr) : (unit, TypeError.type_error) result =
  let unimap = UnificationMap.freeze () in
  let unirowmap = UnificationRowMap.freeze () in
  let result = solve_constraint_expr Unification.unify_type_ted con in
  result |> Result.map_error (fun err ->
    UnificationRowMap.restore unirowmap;
    UnificationMap.restore unimap;
    err
  )


let try_constraint ((_, Constraint(con, alts)) : mono_type_constraint) : (unit, TypeError.type_error) result =
  Printf.printf "trying %s ... " (Display.show_mono_type_constraint_expr con);
  try_constraint_expr con
  |> Result.map (fun () -> Printf.printf "ok\n")
  |> Result.map_error (fun err ->
    Printf.printf "failed\n";
    let attr =
      alts |> List.fold_left (fun acc alt ->
        match (acc, alt) with
        | (Some(acc), _) -> Some(acc)
        | (None, (_, ConstraintBranch(expr, attr))) ->
            begin
              Printf.printf "  trying %s ... " (Display.show_mono_type_constraint_expr expr);
              match try_constraint_expr expr with
              | Ok(()) -> Printf.printf "ok\n"; Some(attr)
              | Error(_) -> Printf.printf "failed\n"; None
            end
        | (None, (_, ConstraintBranchAny(attr))) ->
            Printf.printf "  using fallback message\n";
            Some(attr)
      ) None
    in
    TypeError.ConstraintError(attr, err)
  )


let apply_constraints_poly (lev : level) (qtfbl : quantifiability) (pty : poly_type) : (poly_type, TypeError.type_error) result =
  let open ResultMonad in
  match pty with
  | Poly(_, []) -> return pty
  | _ ->
      let (mty, cons) = TypeConv.instantiate (Level.succ lev) qtfbl pty in
      let* _ = cons |> mapM (fun (_, Constraint(con, _)) -> solve_constraint_expr Unification.unify_type con) in
      let pty = TypeConv.generalize lev mty [] in
      return pty
