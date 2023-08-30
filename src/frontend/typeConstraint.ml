open Types


type explore_result =
  | Unexplored of TypeError.type_error
  | Explored of TypeError.type_error


let make_group (crefs : mono_type_constraint_reference list) (cids : TypeConstraintID.t list) : mono_type_constraint_reference list =
  if List.length crefs = 0 then
    []
  else
    [ConstraintRefGroup(crefs, cids)]


let solve_constraint (unifier : mono_type -> mono_type -> (unit, TypeError.unification_error) result) ((_, con) : mono_type_constraint) : (unit, TypeError.type_error) result =
  match con with
  | ConstraintEqual(lhs, rhs) ->
      unifier lhs rhs
      |> Result.map_error (fun uerr -> TypeError.TypeUnificationError(lhs, rhs, uerr))
  | ConstraintIdentity ->
      Ok(())


let try_constraint (con : mono_type_constraint) : (unit, TypeError.type_error) result =
  (* TED: JUST FOR DEBUG START *)
  let () =
    Printf.printf "trying %s ... " (Display.show_mono_type_constraint con);
  in
  (* TED: JUST FOR DEBUG END*)
  let unimap = UnificationMap.freeze () in
  let unirowmap = UnificationRowMap.freeze () in
  let result = solve_constraint Unification.unify_type_ted con in
  result
  |> Result.map (fun r ->
    Printf.printf "ok\n";
    r
  )
  |> Result.map_error (fun err ->
    Printf.printf "failed\n";
    UnificationRowMap.restore unirowmap;
    UnificationMap.restore unimap;
    err
  )


let apply_substituion (subst : mono_type_substitution) (subst_row : mono_row_substitution) ((range, con) : poly_type_constraint) : mono_type_constraint =
  match con with
  | ConstraintEqual(lhs, rhs) ->
      let lhs = lhs |> TypeConv.instantiate_by_map_ted subst subst_row in
      let rhs = rhs |> TypeConv.instantiate_by_map_ted subst subst_row in
      (range, ConstraintEqual(lhs, rhs))
  | ConstraintIdentity ->
      (range, ConstraintIdentity)


let select_constraints (cids : TypeConstraintID.t list) (change_count : int) : (poly_type_constraint TypeConstraintIDMap.t * type_constraint_attribute list) list =
  let rec aux n xs =
    if n = 0 then
      [([], [])]
    else
      match xs with
      | [] -> []
      | cid :: rest ->
          let use_alts =
            let alts =
              match TypeConstraintSelectionMap.find_opt cid with
              | Some((_, ConstraintSelection(_, alts))) -> alts
              | None -> assert false (* cid should always be found in map *)
            in
            aux (n - 1) rest |> List.concat_map (fun (cons, attrs) ->
              alts |> List.map (fun alt ->
                match alt with
                | (_, ConstraintBranch(con, attr)) -> ((cid, con) :: cons, attr :: attrs)
                | (r, ConstraintBranchAny(attr)) -> ((cid, (r, ConstraintIdentity)) :: cons, attr :: attrs)
              )
            )
          in
          aux n rest @ use_alts
  in
  let candidates = aux change_count cids in
  candidates |> List.map (fun (cons, attrs) -> (cons |> List.to_seq |> TypeConstraintIDMap.of_seq, attrs))


let resolve_constraint_id (selected_map : poly_type_constraint TypeConstraintIDMap.t) (tcid : TypeConstraintID.t) =
  match selected_map |> TypeConstraintIDMap.find_opt tcid with
  | Some(con) -> con
  | None ->
      begin
        match TypeConstraintSelectionMap.find_opt tcid with
        | Some((_, ConstraintSelection(con, _))) -> con
        | None -> assert false
      end


let try_solving (crefs : mono_type_constraint_reference list) (cids : TypeConstraintID.t list) : (unit, TypeError.type_error) result =
  let open ResultMonad in
  if List.length crefs = 0 then
    return ()
  else
    let rec traverse selected_map on_error cursor =
      match cursor with
      | ConstraintRef(subst, subst_row, tcid) ->
          let poly_con = resolve_constraint_id selected_map tcid in
          let mono_con = poly_con |> apply_substituion subst subst_row in
          try_constraint mono_con |> Result.map_error (fun e -> Unexplored(e))
      | ConstraintRefGroup(crefs, cids) ->
          let unimap = UnificationMap.freeze () in
          let unirowmap = UnificationRowMap.freeze () in
          match crefs |> iterM (traverse selected_map on_error) with
          | Error(Unexplored(e)) ->
              (* Restore the state. *)
              UnificationRowMap.restore unirowmap;
              UnificationMap.restore unimap;
              (* TED: TODO: Should cids of child elements also be considered? *)
              err @@ Explored(on_error cursor cids e)
          | other -> other
    in
    let try_alternatives search_base cids original_error =
      Printf.printf " ---- ---- try alternatives ---- ----\n";
      let on_error _ _ e = e in
      let patterns = select_constraints cids 1 in
      let fix = patterns |> List.fold_left (fun fix (selected_map, attrs) ->
        match fix with
        | Some(_) -> fix (* Already found. *)
        | None ->
            match traverse selected_map on_error search_base with
            | Ok(_) ->
                (* This fix actually eliminated the type error. *)
                Some(TypeError.ConstraintError(attrs, original_error))
            | Error(_) ->
                (* The error remains, so try other candidate fixes. *)
                Printf.printf " ---- ---- ---- ------ ---- ---- ----\n";
                None
      ) None in
      Option.value fix ~default:original_error
    in
    (* We first check the default constraints are satisfiable. If it fails, try alternative constraints. *)
    traverse TypeConstraintIDMap.empty try_alternatives (ConstraintRefGroup(crefs, cids))
    |> Result.map_error (function
      | Explored(e) -> e
      | _ -> assert false
    )


let apply_constraints_mono (crefs : mono_type_constraint_reference list) : (unit, TypeError.type_error) result =
  let open ResultMonad in
  let rec traverse = function
    | ConstraintRef(subst, subst_row, tcid) ->
        let poly_con = resolve_constraint_id TypeConstraintIDMap.empty tcid in
        let mono_con = poly_con |> apply_substituion subst subst_row in
        solve_constraint Unification.unify_type mono_con
    | ConstraintRefGroup(crefs, _) ->
        crefs |> iterM traverse
  in
  traverse (ConstraintRefGroup(crefs, []))


let apply_constraints_poly (lev : level) (qtfbl : quantifiability) (pty : poly_type) : (poly_type, TypeError.type_error) result =
  let open ResultMonad in
  match pty with
  | Poly(_, [], []) -> return pty
  | _ ->
      let (mty, crefs, _) = TypeConv.instantiate (Level.succ lev) qtfbl pty in
      let* () = apply_constraints_mono crefs in
      let pty = TypeConv.generalize lev mty [] [] in
      return pty
